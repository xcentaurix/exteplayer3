/*
 * DreamNextGen (AMLogic dreamone/dreamtwo) ALSA audio output.
 *
 * Replaces the linuxdvb_mipsel audio path for boxes that don't have a
 * kernel-side ES audio decoder. We force every codec through software
 * decode (see SetupSoftwareDecoders() called from main), so the bytes
 * arriving in Write() are interleaved S16 PCM and pcmPrivateData_t in
 * extradata carries rate/channels.
 *
 * Kernel /sys/class/tsync is disabled while we own audio so the kernel
 * video decoder runs free — exactly the same approach dream_alsa uses
 * for the GStreamer dreamaudiosink path. Userspace AV-sync polishing
 * lives outside this module.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <inttypes.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/prctl.h>

#include <alsa/asoundlib.h>

#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavformat/avio.h>
#include <libavutil/dict.h>
#include <libavutil/mem.h>
#include <libavutil/channel_layout.h>

#include "common.h"
#include "output.h"
#include "debug.h"
#include "misc.h"
#include "pcm.h"
#include "manager.h"

#define cERR_DREAMAUDIO_NO_ERROR   0
#define cERR_DREAMAUDIO_ERROR     -1

/* Dual-log to stderr (consumed by serviceapp PlayerApp::stderrAvail) AND
 * to /tmp/dream_audio.log. serviceapp filters non-JSON stderr lines from
 * the e2 debug log, so the file is the only reliable place to grep for
 * the sync timeline. */
static void da_log_emit(const char *line);
#define DA_DBG(fmt, ...) do { \
    char _da_buf[512]; \
    int _da_n = snprintf(_da_buf, sizeof(_da_buf), "[dream_audio] " fmt, ##__VA_ARGS__); \
    fprintf(stderr, "%s\n", _da_buf); \
    if (_da_n > 0) da_log_emit(_da_buf); \
} while (0)

#define ALSA_DEVICE_DEFAULT     "default"
#define ALSA_OPEN_MAX_RETRIES   5
#define ALSA_OPEN_RETRY_MS      50
/* 1024 × 8 = 170ms @ 48k, matches /etc/asound.conf dmix slave. */
#define ALSA_PERIOD_FRAMES_AT_48K  1024
#define ALSA_NUM_PERIODS           8
#define ALSA_PREBUFFER_MS          50
#define ALSA_PREFILL_MS            100

#define TSYNC_ENABLE            "/sys/class/tsync/enable"
#define TSYNC_MODE              "/sys/class/tsync/mode"
#define TSYNC_PTS_AUDIO         "/sys/class/tsync/pts_audio"
#define TSYNC_DISCONTINUE       "/sys/class/tsync/discontinue"
/* kernel tsync mode values (TSYNC_MODE_*). */
#define TSYNC_MODE_VMASTER      0
#define TSYNC_MODE_AMASTER      1
#define TSYNC_MODE_PCRMASTER    2

/* ----- IEC61937 / AML passthrough ------------------------------------- */
#define SYNCWORD1               0xF872
#define SYNCWORD2               0x4E1F
#define IEC61937_AC3            0x01
#define IEC61937_DTS1           0x0B
#define IEC61937_DTS2           0x0C
#define IEC61937_DTS3           0x0D
#define IEC61937_EAC3           0x15
#define SPDIF_AC3_BUF_BYTES     6144
#define SPDIF_EAC3_BUF_BYTES    24576
#define DIGITAL_RAW_PCM         0
#define DIGITAL_RAW_SPDIF       1
#define AML_DIGITAL_RAW_PATH    "/sys/class/audiodsp/digital_raw"
#define AML_DIGITAL_CODEC_PATH  "/sys/class/audiodsp/digital_codec"

/* ----- state ---------------------------------------------------------- */

static pthread_mutex_t da_mutex = PTHREAD_MUTEX_INITIALIZER;
static snd_pcm_t      *da_handle = NULL;
static unsigned int    da_rate = 0;
static unsigned int    da_channels = 0;
static int             da_configured = 0;
static int             da_paused = 0;
static int             da_running = 0;
static unsigned long long da_current_pts = 0;

static char           *da_device_name = NULL;   /* strdup'd on open, freed on close */

static int             da_saved_tsync_enable  = -1;

/* Userspace AV-sync state: anchor + sustained-lag recovery. */
static int             da_pts_video_fd = -1;
static int             da_anchor_armed = 0;
static size_t          da_skip_bytes_remaining = 0;
static int64_t         da_last_reanchor_ms  = 0;
static int64_t         da_last_huge_gap_ms  = 0;
static int64_t         da_drift_outside_since_ms = 0;
static int64_t         da_last_sync_log_ms  = 0;
/* vpts-frozen suppression: when the kernel video decoder stalls (DASH
 * segment underrun on hr-live etc.) pts_video stops advancing and the
 * anchor would otherwise flush ALSA + push silence on every cycle. Skip
 * destructive actions while frozen, audio keeps playing. */
static int64_t         da_last_seen_vpts        = -1;
static int64_t         da_last_vpts_change_ms   = 0;
#define DA_VPTS_FROZEN_MS  2000

/* Active passthrough codec: 1=AC3, 2=EAC3, 3=DTS (IEC61937 bursts),
 * 4=TrueHD, 5=DTS-HD MA (HBR via libavformat spdif muxer). */
static int             da_pt_codec = 0;
static int             da_pt_saved_raw = -1;
static int             da_pt_saved_codec = -1;
static int             da_pt_saved_spdif_fmt = -1;
static uint16_t        da_pt_spdif[SPDIF_EAC3_BUF_BYTES / 2];
static int             da_pt_eac3_index = 0;
static int             da_pt_eac3_count = 0;

/* HBR muxer state — emits whole 16-byte (8ch * S16) ALSA frames @ 192 kHz. */
#define DA_HBR_AVIO_BUFSIZE   (128 * 1024)
#define DA_HBR_OUT_INIT_CAP   (128 * 1024)
static AVFormatContext *da_hbr_fmt    = NULL;
static AVIOContext     *da_hbr_avio   = NULL;
static AVStream        *da_hbr_stream = NULL;
static uint8_t         *da_hbr_buf    = NULL;
static size_t           da_hbr_buf_size = 0;
static size_t           da_hbr_buf_cap  = 0;
static int              da_hbr_header_written = 0;
static int64_t          da_hbr_last_pts = 0;

/* ----- Producer/consumer queue (DreamAudioWrite → consumer thread)
 *
 * DreamAudioWrite runs on FFMPEGThread (container_ffmpeg.c). Without this
 * queue, snd_pcm_writei runs inline there, so any time ALSA fills up the
 * FFMPEGThread blocks in writei → no new av_read_frame → ALSA drains →
 * underrun → drift-loop fires silence prefill. dream_video.c already has
 * dv_q / dv_consumer_main for the same reason. Mirror that here.
 *
 * Item payload is post-decode (PCM scaled S16) or pre-built IEC61937 burst
 * (passthrough). Producer mallocs+memcpys data and pushes; consumer pops,
 * runs drift correction + writei, then frees. */
#define DA_Q_CAP            128
#define DA_Q_PUSH_TIMEOUT_MS 500   /* bounded producer wait, then drop */

typedef struct {
    uint8_t        *data;
    size_t          size;
    int64_t         pts_90k;        /* -1 = INVALID_PTS_VALUE in source */
    unsigned int    rate;
    unsigned int    channels;
    int             is_passthrough; /* 0 = PCM, else value of da_pt_codec at push time */
    unsigned int    pt_rate;        /* 48000 for AC3/EAC3/DTS, 192000 for HBR */
    unsigned int    pt_ch;          /* 2 for AC3/EAC3/DTS, 8 for HBR */
} da_qitem_t;

static da_qitem_t       da_q[DA_Q_CAP];
static int              da_q_head    = 0;     /* producer writes here */
static int              da_q_tail    = 0;     /* consumer reads here  */
static pthread_mutex_t  da_q_mu      = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t   da_q_nonemp  = PTHREAD_COND_INITIALIZER;
static pthread_cond_t   da_q_nonfull = PTHREAD_COND_INITIALIZER;
static pthread_t        da_q_thread;
static int              da_q_running = 0;
static int              da_q_stop    = 0;
static uint64_t         da_q_dropped = 0;       /* push failed (queue full) */

/* Forward decls — the lifecycle handlers (Open/Close/Stop/Flush/Switch)
 * call these but they are defined further down with the queue helpers. */
static void da_q_start(void);
static void da_q_shutdown(void);
static void da_q_drain(void);

/* ----- sysfs helpers -------------------------------------------------- */

static void da_write_sysfs(const char *path, const char *val)
{
    FILE *f = fopen(path, "w");
    if (!f) return;
    fputs(val, f);
    fclose(f);
}

static int da_read_sysfs_int(const char *path)
{
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    int v = -1;
    if (fscanf(f, "%d", &v) != 1) v = -1;
    fclose(f);
    return v;
}

static void da_tsync_set_enabled(int on)
{
    da_write_sysfs(TSYNC_ENABLE, on ? "1" : "0");
}

static void da_tsync_set_mode(int mode)
{
    char buf[8];
    snprintf(buf, sizeof(buf), "%d", mode);
    da_write_sysfs(TSYNC_MODE, buf);
}

static void da_tsync_checkin_apts(uint32_t pts_90khz)
{
    char buf[32];
    snprintf(buf, sizeof(buf), "0x%x", pts_90khz);
    da_write_sysfs(TSYNC_PTS_AUDIO, buf);
}

static void da_tsync_signal_discontinuity(void)
{
    da_write_sysfs(TSYNC_DISCONTINUE, "1");
}

/* ----- Userspace AV-sync drift loop helpers (dream_alsa.c port) -------- */

static void da_log_emit(const char *line)
{
    static FILE *fp = NULL;
    static int   tried = 0;
    if (!fp && !tried) {
        tried = 1;
        fp = fopen("/tmp/dream_audio.log", "a");
        if (fp) setvbuf(fp, NULL, _IOLBF, 0);
    }
    if (!fp) return;
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    struct tm tm;
    localtime_r(&ts.tv_sec, &tm);
    fprintf(fp, "%02d:%02d:%02d.%03ld %s\n",
            tm.tm_hour, tm.tm_min, tm.tm_sec, ts.tv_nsec / 1000000, line);
}

static int64_t da_monotonic_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int64_t da_read_pts_video(void)
{
    if (da_pts_video_fd < 0) {
        da_pts_video_fd = open("/sys/class/tsync/pts_video", O_RDONLY | O_CLOEXEC);
        if (da_pts_video_fd < 0) return -1;
    }
    char buf[32];
    if (lseek(da_pts_video_fd, 0, SEEK_SET) < 0) return -1;
    ssize_t n = read(da_pts_video_fd, buf, sizeof(buf) - 1);
    if (n <= 0) return -1;
    buf[n] = 0;
    return (int64_t)strtoll(buf, NULL, 0);
}

/* Push N ms of silence into ALSA. Caller holds da_mutex. */
static void da_push_silence_ms(int ms)
{
    if (!da_handle || !da_configured || ms <= 0) return;
    const size_t fb = (size_t)da_channels * sizeof(int16_t);
    if (fb == 0) return;
    static const uint8_t sil[8192] = { 0 };
    snd_pcm_uframes_t frames_total = (snd_pcm_uframes_t)((int64_t)ms * da_rate / 1000);
    snd_pcm_uframes_t chunk_frames = sizeof(sil) / fb;
    while (frames_total > 0) {
        snd_pcm_uframes_t n = frames_total > chunk_frames ? chunk_frames : frames_total;
        snd_pcm_sframes_t w = snd_pcm_writei(da_handle, sil, n);
        if (w < 0) { if (snd_pcm_recover(da_handle, (int)w, 1) < 0) break; continue; }
        if (w == 0) { usleep(1000); continue; }
        frames_total -= (snd_pcm_uframes_t)w;
    }
}

static void da_write_sysfs_int(const char *path, int v)
{
    char buf[16];
    snprintf(buf, sizeof(buf), "%d", v);
    da_write_sysfs(path, buf);
}

/* ----- enigma2 settings reader (lightweight, no e2 headers) ---------- */

static int da_read_enigma2_setting(const char *key, char *out, size_t out_sz)
{
    FILE *f = fopen("/etc/enigma2/settings", "r");
    if (!f) return 0;
    char line[256];
    const size_t klen = strlen(key);
    int hit = 0;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, key, klen) != 0) continue;
        if (line[klen] != '=') continue;
        const char *val = line + klen + 1;
        char *nl = strchr((char *)val, '\n'); if (nl) *nl = 0;
        snprintf(out, out_sz, "%s", val);
        hit = 1;
        break;
    }
    fclose(f);
    return hit;
}

/* ----- ALSA mixer "Audio spdif format" (enum) ------------------------- */

static int da_get_spdif_format(void)
{
    snd_ctl_t *ctl = NULL;
    if (snd_ctl_open(&ctl, "hw:0", 0) != 0) return -1;
    snd_ctl_elem_id_t    *id;  snd_ctl_elem_id_alloca(&id);
    snd_ctl_elem_value_t *val; snd_ctl_elem_value_alloca(&val);
    snd_ctl_elem_id_set_interface(id, SND_CTL_ELEM_IFACE_MIXER);
    snd_ctl_elem_id_set_name(id, "Audio spdif format");
    snd_ctl_elem_value_set_id(val, id);
    int rc = snd_ctl_elem_read(ctl, val);
    int cur = (rc == 0) ? (int)snd_ctl_elem_value_get_enumerated(val, 0) : -1;
    snd_ctl_close(ctl);
    return cur;
}

static void da_set_spdif_format(int enum_val)
{
    snd_ctl_t *ctl = NULL;
    if (snd_ctl_open(&ctl, "hw:0", 0) != 0) return;
    snd_ctl_elem_id_t    *id;  snd_ctl_elem_id_alloca(&id);
    snd_ctl_elem_value_t *val; snd_ctl_elem_value_alloca(&val);
    snd_ctl_elem_id_set_interface(id, SND_CTL_ELEM_IFACE_MIXER);
    snd_ctl_elem_id_set_name(id, "Audio spdif format");
    snd_ctl_elem_value_set_id(val, id);
    snd_ctl_elem_value_set_enumerated(val, 0, (unsigned int)enum_val);
    snd_ctl_elem_write(ctl, val);
    snd_ctl_close(ctl);
}

/* ----- Passthrough decision ------------------------------------------ */

/* Returns 1 for AC3, 2 for EAC3, 3 for DTS — 0 if no passthrough. */
static int da_passthrough_codec_for(const char *encoding)
{
    if (!encoding) return 0;

    /* digital_raw=0 → decode to PCM regardless of per-codec settings. */
    if (da_read_sysfs_int(AML_DIGITAL_RAW_PATH) <= 0) return 0;

    char val[64];
    if (strcmp(encoding, "A_AC3") == 0) {
        /* No per-codec enigma2 toggle for plain AC3 — digital_raw is it. */
        return 1;
    }
    if (strcmp(encoding, "A_EAC3") == 0) {
        if (!da_read_enigma2_setting("config.av.transcodeac3plus", val, sizeof(val)))
            return 2;   /* default: passthrough */
        if (strcmp(val, "passthrough") == 0) return 2;
        if (strcmp(val, "use_hdmi_caps") == 0) return 2;
        return 0;       /* "force_ac3" / "multichannel" → SW decode */
    }
    if (strcmp(encoding, "A_DTS") == 0) {
        if (!da_read_enigma2_setting("config.av.dtshd", val, sizeof(val)))
            return 0;
        if (strcmp(val, "downmix") == 0) return 0;
        return 3;       /* "passthrough" / "use_hdmi_caps" / "force_ac3" */
    }
    return 0;
}

/* ----- IEC61937 burst builders ---------------------------------------- */

/* Pairwise byte-swap (codec frame BE → ALSA S16 LE). Inline since glibc's
 * swab() needs _DEFAULT_SOURCE which the build doesn't define. */
static void da_byteswap16(const uint8_t *src, uint8_t *dst, size_t n)
{
    size_t pairs = n >> 1;
    for (size_t i = 0; i < pairs; i++) {
        dst[2*i]     = src[2*i + 1];
        dst[2*i + 1] = src[2*i];
    }
    if (n & 1) dst[n - 1] = 0;
}

static int da_pt_build_ac3(const uint8_t *data, int size, uint8_t **out_buf, size_t *out_size)
{
    if (SPDIF_AC3_BUF_BYTES < size + 8) return -1;
    da_write_sysfs_int(AML_DIGITAL_CODEC_PATH, 2);

    uint16_t *out = da_pt_spdif;
    out[0] = SYNCWORD1;
    out[1] = SYNCWORD2;
    out[2] = (uint16_t)(IEC61937_AC3 | (data[5] & 0x07) << 8);
    out[3] = (uint16_t)(size * 8);

    da_byteswap16(data, (uint8_t *)(out + 4), (size_t)size);
    memset((uint8_t *)(out + 4) + size, 0, SPDIF_AC3_BUF_BYTES - 8 - size);

    *out_buf  = (uint8_t *)out;
    *out_size = SPDIF_AC3_BUF_BYTES;
    return 0;
}

static int da_pt_build_eac3(const uint8_t *data, int size, uint8_t **out_buf, size_t *out_size)
{
    if (SPDIF_EAC3_BUF_BYTES < da_pt_eac3_index + size + 8) return -1;

    int repeat = 1;
    int bsid = data[5] >> 3;
    if (bsid > 10 && (data[4] & 0xc0) != 0xc0) {
        static const uint8_t eac3_repeat[4] = { 6, 3, 2, 1 };
        repeat = eac3_repeat[(data[4] & 0x30) >> 4];
    }

    da_write_sysfs_int(AML_DIGITAL_CODEC_PATH, 4);

    uint16_t *out = da_pt_spdif;
    da_byteswap16(data, (uint8_t *)(out + 4) + da_pt_eac3_index, (size_t)size);
    da_pt_eac3_index += size;
    if (++da_pt_eac3_count < repeat) {
        *out_buf  = NULL;
        *out_size = 0;
        return 0;
    }

    out[0] = SYNCWORD1;
    out[1] = SYNCWORD2;
    out[2] = IEC61937_EAC3;
    out[3] = (uint16_t)(da_pt_eac3_index * 8);
    memset((uint8_t *)(out + 4) + da_pt_eac3_index, 0,
           SPDIF_EAC3_BUF_BYTES - 8 - da_pt_eac3_index);

    *out_buf  = (uint8_t *)out;
    *out_size = SPDIF_EAC3_BUF_BYTES;

    da_pt_eac3_index = 0;
    da_pt_eac3_count = 0;
    return 0;
}

static int da_pt_build_dts(const uint8_t *data, int size, uint8_t **out_buf, size_t *out_size)
{
    uint8_t nbs = (uint8_t)(((data[4] & 0x01) << 6) | ((data[5] >> 2) & 0x3f));
    int bsid, burst_sz;
    switch (nbs) {
        case 0x07: bsid = 0x0a;          burst_sz = 1024; break;
        case 0x0f: bsid = IEC61937_DTS1; burst_sz = 2048; break;
        case 0x1f: bsid = IEC61937_DTS2; burst_sz = 4096; break;
        case 0x3f: bsid = IEC61937_DTS3; burst_sz = 8192; break;
        default:
            bsid = 0x00;
            if (nbs < 5) nbs = 127;
            burst_sz = (nbs + 1) * 32 * 2 + 2;
            break;
    }
    if (burst_sz < size + 8) return -1;

    da_write_sysfs_int(AML_DIGITAL_CODEC_PATH, 1);

    uint16_t *out = da_pt_spdif;
    out[0] = SYNCWORD1;
    out[1] = SYNCWORD2;
    out[2] = (uint16_t)bsid;
    out[3] = (uint16_t)(size * 8);
    out[4] = 0x7FFE;
    out[5] = 0x8001;

    da_byteswap16(data, (uint8_t *)(out + 4), (size_t)size);
    memset((uint8_t *)(out + 4) + size, 0, burst_sz - 8 - size);

    *out_buf  = (uint8_t *)out;
    *out_size = (size_t)burst_sz;
    return 0;
}

/* ----- HBR (TrueHD / DTS-HD MA) muxer --------------------------------- */

static int da_sink_has_codec(const char *name, int require_192k)
{
    FILE *f = fopen("/sys/class/amhdmitx/amhdmitx0/aud_cap", "r");
    if (!f) return 0;
    char line[256];
    int hit = 0;
    const size_t nlen = strlen(name);
    while (fgets(line, sizeof(line), f)) {
        const char *p = line;
        while (*p == ' ' || *p == '\t') ++p;
        if (strncmp(p, name, nlen) == 0 && (p[nlen] == ',' || p[nlen] == ' ')) {
            if (!require_192k || strstr(line, "192")) hit = 1;
            break;
        }
    }
    fclose(f);
    return hit;
}

static int da_read_truehd_disabled(void)
{
    char val[64];
    if (!da_read_enigma2_setting("config.av.truehd", val, sizeof(val)))
        return 0;   /* default: try HBR */
    return strcmp(val, "downmix") == 0;
}

/* Returns target da_pt_codec for HBR or 0 if not HBR-eligible. */
static int da_passthrough_hbr_for(const char *encoding)
{
    if (!encoding) return 0;
    char val[64];

    if (strcmp(encoding, "A_TRUEHD") == 0) {
        if (da_read_truehd_disabled()) return 0;
        return (da_sink_has_codec("TrueHD", 1) || da_sink_has_codec("MAT", 1))
               ? 4 : 0;
    }
    /* DTS only goes HBR when the sink advertises 192 kHz DTS-HD. */
    if (strcmp(encoding, "A_DTS") == 0) {
        if (!da_read_enigma2_setting("config.av.dtshd", val, sizeof(val)))
            return 0;
        if (strcmp(val, "downmix") == 0) return 0;
        return da_sink_has_codec("DTS-HD", 1) ? 5 : 0;
    }
    return 0;
}

/* AVIO write callback (non-const buf to match the ffmpeg-ext signature). */
static int da_hbr_write_cb(void *opaque, uint8_t *buf, int buf_size)
{
    (void)opaque;
    size_t need = da_hbr_buf_size + (size_t)buf_size;
    if (need > da_hbr_buf_cap) {
        size_t ncap = da_hbr_buf_cap ? da_hbr_buf_cap * 2 : DA_HBR_OUT_INIT_CAP;
        while (ncap < need) ncap *= 2;
        uint8_t *nb = realloc(da_hbr_buf, ncap);
        if (!nb) return AVERROR(ENOMEM);
        da_hbr_buf = nb;
        da_hbr_buf_cap = ncap;
    }
    memcpy(da_hbr_buf + da_hbr_buf_size, buf, buf_size);
    da_hbr_buf_size += (size_t)buf_size;
    return buf_size;
}

static int da_hbr_start(int hbr_codec)
{
    enum AVCodecID strm;
    int digital_codec_enum;
    int mixer_fmt;

    if (hbr_codec == 4) {           /* TrueHD */
        strm = AV_CODEC_ID_TRUEHD;
        digital_codec_enum = 7;
        mixer_fmt = 7;              /* Audio spdif format: TrueHD */
    } else if (hbr_codec == 5) {    /* DTS-HD MA */
        strm = AV_CODEC_ID_DTS;
        digital_codec_enum = 5;
        mixer_fmt = 8;              /* DTS-HD MA */
    } else return -1;

    da_write_sysfs_int(AML_DIGITAL_CODEC_PATH, digital_codec_enum);
    da_set_spdif_format(mixer_fmt);

    int rc = avformat_alloc_output_context2(&da_hbr_fmt, NULL, "spdif", NULL);
    if (rc < 0 || !da_hbr_fmt) {
        DA_DBG("HBR: alloc spdif muxer: %d", rc);
        return -1;
    }
    da_hbr_stream = avformat_new_stream(da_hbr_fmt, NULL);
    if (!da_hbr_stream) {
        avformat_free_context(da_hbr_fmt); da_hbr_fmt = NULL;
        return -1;
    }
    da_hbr_stream->codecpar->codec_type  = AVMEDIA_TYPE_AUDIO;
    da_hbr_stream->codecpar->codec_id    = strm;
    da_hbr_stream->codecpar->sample_rate = 48000;
    av_channel_layout_default(&da_hbr_stream->codecpar->ch_layout,
                              strm == AV_CODEC_ID_TRUEHD ? 8 : 6);

    uint8_t *avio_buf = av_malloc(DA_HBR_AVIO_BUFSIZE);
    if (!avio_buf) {
        avformat_free_context(da_hbr_fmt); da_hbr_fmt = NULL;
        return -1;
    }
    da_hbr_avio = avio_alloc_context(avio_buf, DA_HBR_AVIO_BUFSIZE, 1, NULL,
                                     NULL, da_hbr_write_cb, NULL);
    if (!da_hbr_avio) {
        av_free(avio_buf);
        avformat_free_context(da_hbr_fmt); da_hbr_fmt = NULL;
        return -1;
    }
    da_hbr_fmt->pb = da_hbr_avio;
    da_hbr_fmt->flags |= AVFMT_FLAG_CUSTOM_IO;

    AVDictionary *opts = NULL;
    if (strm == AV_CODEC_ID_DTS)
        av_dict_set(&opts, "dtshd_rate", "192000", 0);
    rc = avformat_write_header(da_hbr_fmt, &opts);
    av_dict_free(&opts);
    if (rc < 0) {
        DA_DBG("HBR: avformat_write_header: %d", rc);
        return -1;
    }
    da_hbr_header_written = 1;
    da_hbr_buf_cap = DA_HBR_OUT_INIT_CAP;
    da_hbr_buf = malloc(da_hbr_buf_cap);
    if (!da_hbr_buf) return -1;
    DA_DBG("HBR: started codec=%d (digital_codec=%d mixer=%d) 192k/8ch",
           hbr_codec, digital_codec_enum, mixer_fmt);
    return 0;
}

static void da_hbr_stop(void)
{
    if (da_hbr_fmt && da_hbr_header_written) {
        av_write_trailer(da_hbr_fmt);
        da_hbr_header_written = 0;
    }
    if (da_hbr_avio) {
        uint8_t *live = da_hbr_avio->buffer;
        avio_context_free(&da_hbr_avio);
        if (live) av_free(live);
    }
    if (da_hbr_fmt) {
        avformat_free_context(da_hbr_fmt);
        da_hbr_fmt = NULL;
    }
    da_hbr_stream = NULL;
    free(da_hbr_buf);
    da_hbr_buf = NULL;
    da_hbr_buf_size = 0;
    da_hbr_buf_cap = 0;
}

/* Push one TrueHD / DTS-HD-MA codec packet through the muxer; returns
 * buffer pointer + byte count of whole-ALSA-frame (16-byte) chunks ready
 * to write. Tail bytes stay queued for the next push. */
static int da_hbr_push(const uint8_t *data, int size, int64_t pts,
                       uint8_t **out_buf, size_t *out_size)
{
    if (!da_hbr_fmt) return -1;
    AVPacket *pkt = av_packet_alloc();
    if (!pkt) return -1;
    if (av_new_packet(pkt, size) < 0) { av_packet_free(&pkt); return -1; }
    memcpy(pkt->data, data, size);
    pkt->stream_index = da_hbr_stream->index;
    pkt->pts = pts;
    pkt->dts = pts;

    int rc = av_write_frame(da_hbr_fmt, pkt);
    av_packet_free(&pkt);
    if (rc < 0) {
        char eb[128]; av_strerror(rc, eb, sizeof(eb));
        DA_DBG("HBR: av_write_frame: %s", eb);
        return -1;
    }
    avio_flush(da_hbr_avio);

    /* Emit whole 16-byte (8 ch * S16) ALSA frames. */
    size_t frames = da_hbr_buf_size / 16;
    if (frames == 0) { *out_buf = NULL; *out_size = 0; return 0; }
    size_t bytes = frames * 16;
    *out_buf  = da_hbr_buf;
    *out_size = bytes;
    /* Note: caller writes from da_hbr_buf BEFORE we shift — the shift
     * happens in da_hbr_consume() after ALSA write succeeds. */
    return 0;
}

static void da_hbr_consume(size_t bytes)
{
    if (bytes > da_hbr_buf_size) bytes = da_hbr_buf_size;
    if (bytes < da_hbr_buf_size)
        memmove(da_hbr_buf, da_hbr_buf + bytes, da_hbr_buf_size - bytes);
    da_hbr_buf_size -= bytes;
}

/* ----- ALSA wrappers (caller holds da_mutex) -------------------------- */

static int da_alsa_open_handle(void)
{
    const char *dev = da_device_name ? da_device_name : ALSA_DEVICE_DEFAULT;
    int err = 0;
    for (int i = 0; i < ALSA_OPEN_MAX_RETRIES; ++i) {
        err = snd_pcm_open(&da_handle, dev,
                           SND_PCM_STREAM_PLAYBACK, SND_PCM_NONBLOCK);
        if (err == 0) break;
        if (err == -EBUSY && i < ALSA_OPEN_MAX_RETRIES - 1) {
            DA_DBG("open '%s' busy, retry %d/%d", dev, i + 1, ALSA_OPEN_MAX_RETRIES);
            usleep(ALSA_OPEN_RETRY_MS * 1000);
            da_handle = NULL;
            continue;
        }
        DA_DBG("open '%s' failed: %s", dev, snd_strerror(err));
        da_handle = NULL;
        return -1;
    }
    if (!da_handle) return -1;
    snd_pcm_nonblock(da_handle, 0);
    return 0;
}

static void da_alsa_close_handle(void)
{
    if (da_handle) {
        snd_pcm_drop(da_handle);
        snd_pcm_close(da_handle);
        da_handle = NULL;
        usleep(10000);
    }
    da_configured = 0;
    da_rate = 0;
    da_channels = 0;
}

static int da_alsa_setparams(unsigned int rate, unsigned int channels)
{
    if (da_configured && da_rate == rate && da_channels == channels)
        return 0;

    if (da_handle)
        da_alsa_close_handle();
    if (da_alsa_open_handle() < 0)
        return -1;

    snd_pcm_hw_params_t *hw;
    snd_pcm_hw_params_alloca(&hw);
    unsigned int r = rate, ch = channels;
    snd_pcm_hw_params_any(da_handle, hw);
    snd_pcm_hw_params_set_access(da_handle, hw, SND_PCM_ACCESS_RW_INTERLEAVED);
    snd_pcm_hw_params_set_format(da_handle, hw, SND_PCM_FORMAT_S16);
    snd_pcm_hw_params_set_rate_near(da_handle, hw, &r, NULL);
    snd_pcm_hw_params_set_channels_near(da_handle, hw, &ch);

    snd_pcm_uframes_t period_size =
        ((snd_pcm_uframes_t)r * ALSA_PERIOD_FRAMES_AT_48K) / 48000;
    snd_pcm_uframes_t buffer_size = period_size * ALSA_NUM_PERIODS;
    snd_pcm_hw_params_set_period_size_near(da_handle, hw, &period_size, NULL);
    snd_pcm_hw_params_set_buffer_size_near(da_handle, hw, &buffer_size);

    int err = snd_pcm_hw_params(da_handle, hw);
    if (err < 0) {
        DA_DBG("hw_params(rate=%u ch=%u): %s", rate, channels, snd_strerror(err));
        return -1;
    }
    snd_pcm_hw_params_get_period_size(hw, &period_size, NULL);
    snd_pcm_hw_params_get_buffer_size(hw, &buffer_size);

    snd_pcm_uframes_t start_threshold = (r * ALSA_PREBUFFER_MS) / 1000;
    if (start_threshold > buffer_size) start_threshold = buffer_size * 2 / 3;

    /* sw_params: hold device in PREPARED until start_threshold queued;
     * silence-pad on underrun instead of XRUN/EPIPE. */
    snd_pcm_sw_params_t *sw;
    snd_pcm_sw_params_alloca(&sw);
    snd_pcm_sw_params_current(da_handle, sw);
    snd_pcm_uframes_t boundary = 0;
    snd_pcm_sw_params_get_boundary(sw, &boundary);
    snd_pcm_sw_params_set_start_threshold(da_handle, sw, start_threshold);
    snd_pcm_sw_params_set_stop_threshold(da_handle, sw, boundary);
    snd_pcm_sw_params_set_silence_threshold(da_handle, sw, period_size);
    snd_pcm_sw_params_set_silence_size(da_handle, sw, period_size);
    int sw_err = snd_pcm_sw_params(da_handle, sw);
    if (sw_err < 0) DA_DBG("sw_params: %s", snd_strerror(sw_err));

    da_rate = rate;
    da_channels = channels;
    da_configured = 1;

    /* prefill silence so dmix queue doesn't run near-empty on first writei. */
    {
        const size_t fb = (size_t)channels * sizeof(int16_t);
        static const uint8_t sil[8192] = { 0 };
        snd_pcm_uframes_t left = (snd_pcm_uframes_t)rate * ALSA_PREFILL_MS / 1000;
        snd_pcm_uframes_t chunk = sizeof(sil) / (fb ? fb : 1);
        while (left > 0 && chunk > 0) {
            snd_pcm_uframes_t n = (left > chunk) ? chunk : left;
            snd_pcm_sframes_t w = snd_pcm_writei(da_handle, sil, n);
            if (w <= 0) { snd_pcm_prepare(da_handle); break; }
            left -= (snd_pcm_uframes_t)w;
        }
    }

    DA_DBG("configured rate=%u ch=%u period=%lu buf=%lu prefill=%dms",
           rate, channels, (unsigned long)period_size,
           (unsigned long)buffer_size, ALSA_PREFILL_MS);
    return 0;
}

/* Fixed −20 dB SW attenuation (Q15 0.1) to match DVB-broadcast
 * loudness. Streaming sources peak near 0 dBFS; DVB audio is
 * dialnorm-normalised, so without this they're ~20 dB hotter at the
 * same user volume. */
#define DA_PCM_GAIN_Q15  3277

static int da_alsa_write(const uint8_t *data, size_t size)
{
    if (!da_handle || !da_configured || !data || size == 0) return -1;
    const size_t frame_bytes = (size_t)da_channels * sizeof(int16_t);
    if (frame_bytes == 0 || (size % frame_bytes) != 0) return -1;

    int16_t *scaled = (int16_t *)malloc(size);
    if (!scaled) return -1;

    const size_t nsamples = size / sizeof(int16_t);
    const int16_t *src = (const int16_t *)data;
    for (size_t i = 0; i < nsamples; i++) {
        int32_t s = ((int32_t)src[i] * DA_PCM_GAIN_Q15) >> 15;
        if (s >  32767) s =  32767;
        if (s < -32768) s = -32768;
        scaled[i] = (int16_t)s;
    }

    snd_pcm_uframes_t frames = size / frame_bytes;
    size_t offset = 0;
    int ret = (int)size;
    while (frames > 0) {
        snd_pcm_sframes_t n = snd_pcm_writei(da_handle,
                                             (const uint8_t *)scaled + offset, frames);
        if (n < 0) {
            int err = snd_pcm_recover(da_handle, (int)n, 0);
            if (err < 0) {
                DA_DBG("recover: %s", snd_strerror(err));
                ret = -1;
                break;
            }
            continue;
        }
        offset += (size_t)n * frame_bytes;
        frames -= (snd_pcm_uframes_t)n;
    }
    free(scaled);
    return ret;
}

/* ----- Output_t Command handlers -------------------------------------- */

static void da_passthrough_setup(Context_t *context)
{
    da_pt_codec = 0;
    da_pt_eac3_index = 0;
    da_pt_eac3_count = 0;

    if (!context || !context->manager || !context->manager->audio) return;

    char *encoding = NULL;
    context->manager->audio->Command(context, MANAGER_GETENCODING, &encoding);
    if (!encoding) return;

    /* Prefer HBR; fall back to plain IEC61937 burst. */
    int hbr = da_passthrough_hbr_for(encoding);
    int pt  = hbr ? hbr : da_passthrough_codec_for(encoding);
    DA_DBG("passthrough probe: encoding='%s' -> codec=%d (hbr=%d)",
           encoding, pt, hbr);
    free(encoding);
    if (!pt) return;

    /* Save AML state for restore on Close. */
    da_pt_saved_raw        = da_read_sysfs_int(AML_DIGITAL_RAW_PATH);
    da_pt_saved_codec      = da_read_sysfs_int(AML_DIGITAL_CODEC_PATH);
    da_pt_saved_spdif_fmt  = da_get_spdif_format();

    if (hbr) {
        /* HBR: spdif format + digital_codec already set inside da_hbr_start. */
        if (da_hbr_start(hbr) < 0) {
            DA_DBG("HBR start failed — falling back to PCM");
            da_hbr_stop();
            return;
        }
    } else {
        /* Audio spdif format enum: 2=AC3, 4=EAC3, 3=DTS. */
        int mixer_enum = (pt == 1) ? 2 : (pt == 2) ? 4 : 3;
        da_set_spdif_format(mixer_enum);
    }

    da_pt_codec = pt;
    DA_DBG("passthrough ON: codec=%d saved_raw=%d saved_codec=%d saved_fmt=%d",
           pt, da_pt_saved_raw, da_pt_saved_codec, da_pt_saved_spdif_fmt);
}

static void da_passthrough_restore(void)
{
    if (!da_pt_codec) return;
    if (da_pt_codec >= 4) da_hbr_stop();    /* TrueHD / DTS-HD-MA */
    if (da_pt_saved_spdif_fmt >= 0) da_set_spdif_format(da_pt_saved_spdif_fmt);
    if (da_pt_saved_codec   >= 0) da_write_sysfs_int(AML_DIGITAL_CODEC_PATH, da_pt_saved_codec);
    /* leave digital_raw alone — it's a global user toggle, not ours to flip */
    da_pt_codec = 0;
    da_pt_saved_spdif_fmt = -1;
    da_pt_saved_codec     = -1;
    da_pt_saved_raw       = -1;
    da_pt_eac3_index = 0;
    da_pt_eac3_count = 0;
}

static int DreamAudioOpen(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;

    pthread_mutex_lock(&da_mutex);
    if (!da_device_name) {
        const char *dev = getenv("EXTEPLAYER3_ALSA_DEVICE");
        da_device_name = strdup(dev && *dev ? dev : ALSA_DEVICE_DEFAULT);
    }
    /* Match what gstplayer2 actually does (verified via strace) — kernel
     * tsync ENABLED in PCRMASTER, pts_audio fed per chunk in Write. The
     * stale "VMASTER = disable tsync" comment in dream_avsync.c does not
     * reflect dreamaudiosink's runtime behaviour. */
    if (da_saved_tsync_enable < 0)
        da_saved_tsync_enable = da_read_sysfs_int(TSYNC_ENABLE);
    /* Wipe leftover pts from any previous owner (live-TV / earlier
     * gstplayer / earlier exteplayer3 session) so pcrmaster anchors on
     * the new stream rather than the carried-over clock. */
    da_write_sysfs("/sys/class/tsync/pts_audio", "0");
    da_write_sysfs("/sys/class/tsync/pts_video", "0");
    da_tsync_signal_discontinuity();
    /* Match dreamaudiosink (DEFAULT_TSYNC_MODE=2 in gstdreamaudiosink.c).
     * PCRMASTER: kernel uses smoothed pcrscr (synthesized from our
     * pts_audio writes) as the master clock. AMASTER caused the kernel
     * pacer to release video frames at the audio-chunk arrival rate
     * (~50fps for our 20ms chunks), dropping ~33% of frames for 25fps
     * source — visible as the "gefesselt" stutter. */
    da_tsync_set_mode(TSYNC_MODE_PCRMASTER);
    da_tsync_set_enabled(1);
    /* gstdreamaudiosink.c:178 — pcr_offset=0x0 + auto_pcr_offset=0x0
     * snd_pcm_delay() deckt unsere komplette audio queue ab, deshalb keine
     * extra HW-pipeline-latency-Kompensation gegen pts_video nötig. Ohne
     * diese Writes bleibt pcr_offset auf dem von Live-TV's eAVSyncCore
     * gesetzten Wert (75 ms) hängen → pcrscr drifted gegenüber pts_audio. */
    da_write_sysfs("/proc/stb/pcr_offset", "0x0");
    da_write_sysfs("/proc/stb/auto_pcr_offset", "0x0");
    /* Reset sync state; anchor fires on first chunk. */
    da_anchor_armed             = 1;
    da_skip_bytes_remaining     = 0;
    da_last_reanchor_ms         = 0;
    da_last_huge_gap_ms         = 0;
    da_drift_outside_since_ms   = 0;
    da_last_sync_log_ms         = 0;
    da_last_seen_vpts           = -1;
    da_last_vpts_change_ms      = 0;
    int ret = da_alsa_open_handle();
    da_paused = 0;
    da_running = 0;
    da_passthrough_setup(context);
    pthread_mutex_unlock(&da_mutex);

    if (ret < 0) {
        DA_DBG("open failed");
        return cERR_DREAMAUDIO_ERROR;
    }

    /* Start consumer thread last — it expects da_handle ready. */
    da_q_start();

    DA_DBG("opened device='%s' passthrough=%d", da_device_name, da_pt_codec);
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioClose(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;

    /* Stop+join consumer before closing the ALSA handle, otherwise the
     * worker could still be inside snd_pcm_writei. */
    da_q_shutdown();

    pthread_mutex_lock(&da_mutex);
    da_alsa_close_handle();
    da_passthrough_restore();
    da_running = 0;
    da_paused = 0;
    da_current_pts = 0;
    pthread_mutex_unlock(&da_mutex);

    if (da_saved_tsync_enable >= 0) {
        /* signal discontinuity so kernel drops stale pts_audio before
         * the next owner (live-TV's eAVSyncCore) re-enables sync. */
        da_tsync_signal_discontinuity();
        da_tsync_set_enabled(da_saved_tsync_enable);
        da_saved_tsync_enable = -1;
    }
    if (da_pts_video_fd >= 0) { close(da_pts_video_fd); da_pts_video_fd = -1; }
    DA_DBG("closed");
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioPlay(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    pthread_mutex_lock(&da_mutex);
    da_running = 1;
    da_paused = 0;
    da_current_pts = 0;
    pthread_mutex_unlock(&da_mutex);
    DA_DBG("play");
    return cERR_DREAMAUDIO_NO_ERROR;
}

/* Mirror of dream_alsa_reset_anchor() in the dreamaudiosink reference
 * implementation. Called from Stop/Flush/Switch so the first chunk after
 * a seek runs the one-shot anchor cleanly instead of fighting stale
 * vpts/apts state through the HUGE-gap → silence-prefill cascade.
 * Caller must hold da_mutex. */
static void da_reset_anchor_locked(void)
{
    da_anchor_armed             = 1;
    da_skip_bytes_remaining     = 0;
    da_last_reanchor_ms         = 0;
    da_last_huge_gap_ms         = 0;
    da_drift_outside_since_ms   = 0;
    da_last_sync_log_ms         = 0;
    da_last_seen_vpts           = -1;
    da_last_vpts_change_ms      = 0;
}

static int DreamAudioStop(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    da_q_drain();
    pthread_mutex_lock(&da_mutex);
    if (da_handle) {
        snd_pcm_drop(da_handle);
        snd_pcm_prepare(da_handle);
    }
    da_reset_anchor_locked();
    da_running = 0;
    da_current_pts = 0;
    pthread_mutex_unlock(&da_mutex);
    DA_DBG("stop");
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioFlush(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    da_q_drain();
    pthread_mutex_lock(&da_mutex);
    if (da_handle) {
        snd_pcm_drop(da_handle);
        snd_pcm_prepare(da_handle);
    }
    da_reset_anchor_locked();
    da_tsync_signal_discontinuity();
    pthread_mutex_unlock(&da_mutex);
    DA_DBG("flush");
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioPause(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    pthread_mutex_lock(&da_mutex);
    if (da_handle) snd_pcm_pause(da_handle, 1);
    da_paused = 1;
    pthread_mutex_unlock(&da_mutex);
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioContinue(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    pthread_mutex_lock(&da_mutex);
    if (da_handle) snd_pcm_pause(da_handle, 0);
    da_paused = 0;
    pthread_mutex_unlock(&da_mutex);
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioClear(Context_t *context, char *type)
{
    return DreamAudioFlush(context, type);
}

static int DreamAudioSwitch(Context_t *context, char *type)
{
    if (strcmp(type, "audio") != 0) return cERR_DREAMAUDIO_NO_ERROR;
    /* track switch — drop pending buffer + re-evaluate passthrough since
     * the new track may have a different codec */
    da_q_drain();
    pthread_mutex_lock(&da_mutex);
    if (da_handle) {
        snd_pcm_drop(da_handle);
        snd_pcm_prepare(da_handle);
    }
    da_reset_anchor_locked();
    da_passthrough_restore();
    da_passthrough_setup(context);
    pthread_mutex_unlock(&da_mutex);
    da_tsync_signal_discontinuity();
    DA_DBG("switch (passthrough=%d)", da_pt_codec);
    return cERR_DREAMAUDIO_NO_ERROR;
}

static int DreamAudioPts(Context_t *context, unsigned long long *pts)
{
    pthread_mutex_lock(&da_mutex);
    *pts = da_current_pts;
    pthread_mutex_unlock(&da_mutex);
    return cERR_DREAMAUDIO_NO_ERROR;
}

/* ----- Write (the actual PCM hand-off) -------------------------------- */

/* Direct ALSA write without the PCM gain (used for IEC61937 bursts;
 * caller holds da_mutex). */
static int da_alsa_write_raw(const uint8_t *data, size_t size)
{
    if (!da_handle || !da_configured || !data || size == 0) return -1;
    const size_t frame_bytes = (size_t)da_channels * sizeof(int16_t);
    if (frame_bytes == 0 || (size % frame_bytes) != 0) return -1;

    snd_pcm_uframes_t frames = size / frame_bytes;
    size_t offset = 0;
    while (frames > 0) {
        snd_pcm_sframes_t n = snd_pcm_writei(da_handle, data + offset, frames);
        if (n < 0) {
            int err = snd_pcm_recover(da_handle, (int)n, 0);
            if (err < 0) { DA_DBG("recover: %s", snd_strerror(err)); return -1; }
            continue;
        }
        offset += (size_t)n * frame_bytes;
        frames -= (snd_pcm_uframes_t)n;
    }
    return (int)size;
}

/* ----- Producer/consumer queue helpers + consumer thread -------------- */

static int da_q_is_full_locked(void)  { return ((da_q_head + 1) % DA_Q_CAP) == da_q_tail; }
static int da_q_is_empty_locked(void) { return da_q_head == da_q_tail; }

static int da_q_depth_locked(void)
{
    return (da_q_head - da_q_tail + DA_Q_CAP) % DA_Q_CAP;
}

/* Push: caller transfers data ownership into queue on success.
 * Bounded wait DA_Q_PUSH_TIMEOUT_MS, then drop.
 * Return 0 = pushed (caller must NOT free), -1 = dropped (caller still owns). */
static int da_q_push(da_qitem_t *src)
{
    pthread_mutex_lock(&da_q_mu);
    struct timespec deadline;
    clock_gettime(CLOCK_REALTIME, &deadline);
    deadline.tv_nsec += (long)DA_Q_PUSH_TIMEOUT_MS * 1000000L;
    if (deadline.tv_nsec >= 1000000000L) {
        deadline.tv_sec  += deadline.tv_nsec / 1000000000L;
        deadline.tv_nsec %= 1000000000L;
    }
    while (da_q_is_full_locked() && !da_q_stop) {
        if (pthread_cond_timedwait(&da_q_nonfull, &da_q_mu, &deadline) != 0) break;
    }
    if (da_q_is_full_locked() || da_q_stop) {
        da_q_dropped++;
        pthread_mutex_unlock(&da_q_mu);
        return -1;
    }
    da_q[da_q_head] = *src;
    da_q_head = (da_q_head + 1) % DA_Q_CAP;
    pthread_cond_signal(&da_q_nonemp);
    pthread_mutex_unlock(&da_q_mu);
    return 0;
}

/* Pop: blocks until item available or shutdown. Returns 0 with *out filled
 * (consumer takes ownership of out->data) or -1 on shutdown with empty queue. */
static int da_q_pop(da_qitem_t *out)
{
    pthread_mutex_lock(&da_q_mu);
    while (da_q_is_empty_locked() && !da_q_stop) {
        pthread_cond_wait(&da_q_nonemp, &da_q_mu);
    }
    if (da_q_stop && da_q_is_empty_locked()) {
        pthread_mutex_unlock(&da_q_mu);
        return -1;
    }
    *out = da_q[da_q_tail];
    da_q_tail = (da_q_tail + 1) % DA_Q_CAP;
    pthread_cond_signal(&da_q_nonfull);
    pthread_mutex_unlock(&da_q_mu);
    return 0;
}

static void da_q_drain(void)
{
    pthread_mutex_lock(&da_q_mu);
    while (!da_q_is_empty_locked()) {
        free(da_q[da_q_tail].data);
        da_q[da_q_tail].data = NULL;
        da_q_tail = (da_q_tail + 1) % DA_Q_CAP;
    }
    da_q_head = da_q_tail = 0;
    pthread_cond_broadcast(&da_q_nonfull);
    pthread_mutex_unlock(&da_q_mu);
}

/* Consumer thread: pop item, run drift correction, writei, free.
 * Mirrors dream_video.c dv_consumer_main: producer (FFMPEGThread) stays
 * free to call av_read_frame so ALSA doesn't drain into underrun. */
static void *da_consumer_main(void *arg)
{
    (void)arg;
    char tn[16] = "da_consumer";
    prctl(PR_SET_NAME, (unsigned long)tn, 0, 0, 0);

    while (!da_q_stop) {
        da_qitem_t item;
        if (da_q_pop(&item) < 0) break;

        pthread_mutex_lock(&da_mutex);

        if (!da_handle || da_paused) {
            pthread_mutex_unlock(&da_mutex);
            free(item.data);
            continue;
        }

        unsigned int rate     = item.is_passthrough ? item.pt_rate : item.rate;
        unsigned int channels = item.is_passthrough ? item.pt_ch   : item.channels;
        if (da_alsa_setparams(rate, channels) < 0) {
            pthread_mutex_unlock(&da_mutex);
            free(item.data);
            continue;
        }

        /* PTS → tsync pts_audio (apts_speaker = chunk_pts - snd_pcm_delay).
         * Same as the in-line path was doing in the producer before. */
        int64_t apts_speaker   = -1;
        int64_t alsa_delay_pts = 0;
        if (item.pts_90k >= 0) {
            da_current_pts = (unsigned long long)item.pts_90k;
            snd_pcm_sframes_t df = 0;
            if (rate && snd_pcm_delay(da_handle, &df) == 0 && df > 0)
                alsa_delay_pts = (int64_t)df * 90000LL / (int64_t)rate;
            apts_speaker = item.pts_90k - alsa_delay_pts;
            if (apts_speaker >= 0)
                da_tsync_checkin_apts((uint32_t)apts_speaker);
        }

        if (item.is_passthrough) {
            (void)da_alsa_write_raw(item.data, item.size);
            pthread_mutex_unlock(&da_mutex);
            free(item.data);
            continue;
        }

        /* ----- PCM: drift correction (anchor + mini-skip + re-arm) ----- */
        const uint8_t *write_data = item.data;
        size_t          write_len = item.size;
        const size_t    fb        = (size_t)channels * sizeof(int16_t);

        if (da_skip_bytes_remaining > 0) {
            size_t drop = da_skip_bytes_remaining > write_len ? write_len : da_skip_bytes_remaining;
            if (fb) drop -= (drop % fb);
            if (drop > 0) {
                da_skip_bytes_remaining -= drop;
                write_data += drop;
                write_len  -= drop;
            }
        }

        if (da_anchor_armed && apts_speaker >= 0 && rate && fb) {
            int64_t pts_v = da_read_pts_video();
            if (pts_v >= 0) {
                int64_t now_ms_hg = da_monotonic_ms();
                if (pts_v != da_last_seen_vpts) {
                    da_last_seen_vpts      = pts_v;
                    da_last_vpts_change_ms = now_ms_hg;
                }
                int vpts_frozen = (da_last_vpts_change_ms != 0
                                   && now_ms_hg - da_last_vpts_change_ms > DA_VPTS_FROZEN_MS);

                int32_t lead_ms = (int32_t)((uint32_t)apts_speaker - (uint32_t)pts_v) / 90;
                DA_DBG("anchor: lead=%+dms vpts=%lx apts=%lx%s",
                       lead_ms, (long)pts_v, (long)apts_speaker,
                       vpts_frozen ? " [vpts frozen, skip]" : "");
                if (vpts_frozen) {
                    /* Video decoder stalled (DASH segment underrun, etc).
                     * Skip destructive actions, let audio play through.
                     * anchor stays armed so we re-evaluate when vpts moves. */
                } else if ((lead_ms > 2000 || lead_ms < -2000)
                    && now_ms_hg - da_last_huge_gap_ms > 1000)
                {
                    da_last_huge_gap_ms = now_ms_hg;
                    snd_pcm_drop(da_handle);
                    snd_pcm_prepare(da_handle);
                    DA_DBG("anchor: HUGE gap %+dms → ALSA flush, drop buffer (1s throttle)", lead_ms);
                    pthread_mutex_unlock(&da_mutex);
                    free(item.data);
                    continue;
                } else if (lead_ms > 50) {
                    int adj = lead_ms > 2000 ? 2000 : lead_ms;
                    da_push_silence_ms(adj);
                    DA_DBG("anchor: pushed %dms silence (was %+dms ahead)", adj, lead_ms);
                    da_anchor_armed = 0;
                } else if (lead_ms < -50) {
                    int adj = lead_ms < -3000 ? -3000 : lead_ms;
                    da_skip_bytes_remaining =
                        (size_t)((int64_t)(-adj) * (int64_t)rate / 1000) * fb;
                    DA_DBG("anchor: queued %dms skip (was %+dms behind)", -adj, lead_ms);
                    size_t drop = da_skip_bytes_remaining > write_len ? write_len : da_skip_bytes_remaining;
                    drop -= (drop % fb);
                    da_skip_bytes_remaining -= drop;
                    write_data += drop;
                    write_len  -= drop;
                    da_anchor_armed = 0;
                } else {
                    da_anchor_armed = 0;
                }
            }
        }

        /* Post-anchor: sustained-lag recovery only. */
        if (!da_anchor_armed && apts_speaker >= 0 && rate && fb) {
            int64_t pts_v = da_read_pts_video();
            if (pts_v >= 0) {
                int32_t av_ms  = (int32_t)((uint32_t)apts_speaker - (uint32_t)pts_v) / 90;
                int64_t now_ms = da_monotonic_ms();
                if (pts_v != da_last_seen_vpts) {
                    da_last_seen_vpts      = pts_v;
                    da_last_vpts_change_ms = now_ms;
                }
                int vpts_frozen = (da_last_vpts_change_ms != 0
                                   && now_ms - da_last_vpts_change_ms > DA_VPTS_FROZEN_MS);

                /* 30s heartbeat. */
                if (now_ms - da_last_sync_log_ms > 30000) {
                    pthread_mutex_lock(&da_q_mu);
                    int qd = da_q_depth_locked();
                    pthread_mutex_unlock(&da_q_mu);
                    DA_DBG("vpts=%lx apts=%lx av=%+dms hw_delay=%lldms q=%d/%d%s [heartbeat]",
                           (long)pts_v, (long)apts_speaker, av_ms,
                           (long long)(alsa_delay_pts / 90), qd, DA_Q_CAP - 1,
                           vpts_frozen ? " VFROZEN" : "");
                    da_last_sync_log_ms = now_ms;
                }

                /* Re-arm anchor when |av| > 1000ms held >=2s; 5s cooldown.
                 * Skipped while vpts is frozen — destructive re-arm would
                 * just flush audio repeatedly. */
                int32_t abs_av = av_ms < 0 ? -av_ms : av_ms;
                if (vpts_frozen) {
                    da_drift_outside_since_ms = 0;
                } else if (abs_av > 1000) {
                    if (da_drift_outside_since_ms == 0)
                        da_drift_outside_since_ms = now_ms;
                } else {
                    da_drift_outside_since_ms = 0;
                }
                if (da_drift_outside_since_ms != 0
                    && now_ms - da_drift_outside_since_ms >= 2000
                    && now_ms - da_last_reanchor_ms > 5000)
                {
                    da_last_reanchor_ms       = now_ms;
                    da_drift_outside_since_ms = 0;
                    da_anchor_armed           = 1;
                    DA_DBG("sustained lag av=%+dms → re-arm anchor", av_ms);
                }
            }
        }

        if (write_len > 0) (void)da_alsa_write(write_data, write_len);

        pthread_mutex_unlock(&da_mutex);
        free(item.data);
    }
    return NULL;
}

static void da_q_start(void)
{
    if (da_q_running) return;
    da_q_stop    = 0;
    da_q_head    = da_q_tail = 0;
    da_q_dropped = 0;
    if (pthread_create(&da_q_thread, NULL, da_consumer_main, NULL) == 0) {
        da_q_running = 1;
    } else {
        DA_DBG("pthread_create consumer failed: %s", strerror(errno));
    }
}

static void da_q_shutdown(void)
{
    if (!da_q_running) return;
    pthread_mutex_lock(&da_q_mu);
    da_q_stop = 1;
    pthread_cond_broadcast(&da_q_nonemp);
    pthread_cond_broadcast(&da_q_nonfull);
    pthread_mutex_unlock(&da_q_mu);
    pthread_join(da_q_thread, NULL);
    da_q_running = 0;
    da_q_drain();
}

/* Producer: validate input, copy payload, enqueue. The consumer thread
 * does setparams + drift correction + snd_pcm_writei so that FFMPEGThread
 * never blocks on ALSA. */
static int DreamAudioWrite(void *_context, void *_out)
{
    (void)_context;
    AudioVideoOut_t *out = (AudioVideoOut_t *)_out;

    if (!out || !out->data || out->len == 0) return cERR_DREAMAUDIO_NO_ERROR;
    if (out->type && strcmp(out->type, "audio") != 0)
        return cERR_DREAMAUDIO_NO_ERROR;
    if (!da_q_running) return cERR_DREAMAUDIO_NO_ERROR;

    int64_t pts_90k = (out->pts != INVALID_PTS_VALUE) ? (int64_t)out->pts : -1;

    /* ----- Passthrough: build IEC61937 burst, copy, enqueue ----- */
    if (da_pt_codec) {
        uint8_t *burst = NULL;
        size_t   burst_sz = 0;
        int rc = -1;
        unsigned int pt_rate = 48000;
        unsigned int pt_ch   = 2;

        if (da_pt_codec >= 4) {
            da_hbr_last_pts = pts_90k >= 0 ? pts_90k : 0;
            rc = da_hbr_push(out->data, (int)out->len, da_hbr_last_pts,
                             &burst, &burst_sz);
            pt_rate = 192000;
            pt_ch   = 8;
        } else {
            switch (da_pt_codec) {
                case 1: rc = da_pt_build_ac3 (out->data, (int)out->len, &burst, &burst_sz); break;
                case 2: rc = da_pt_build_eac3(out->data, (int)out->len, &burst, &burst_sz); break;
                case 3: rc = da_pt_build_dts (out->data, (int)out->len, &burst, &burst_sz); break;
            }
        }
        if (rc < 0) {
            DA_DBG("passthrough build failed (codec=%d len=%u)", da_pt_codec, out->len);
            return cERR_DREAMAUDIO_ERROR;
        }
        if (burst_sz == 0) return cERR_DREAMAUDIO_NO_ERROR;  /* HBR mid-accum / EAC3 partial */

        /* Burst pointer is into static / muxer-owned memory (da_pt_spdif or
         * da_hbr_buf). Copy before queuing so subsequent builds can reuse
         * the buffer; for HBR also advance the muxer's consumed marker. */
        uint8_t *copy = (uint8_t *)malloc(burst_sz);
        if (!copy) return cERR_DREAMAUDIO_ERROR;
        memcpy(copy, burst, burst_sz);
        if (da_pt_codec >= 4) da_hbr_consume(burst_sz);

        da_qitem_t it = {0};
        it.data           = copy;
        it.size           = burst_sz;
        it.pts_90k        = pts_90k;
        it.is_passthrough = da_pt_codec;
        it.pt_rate        = pt_rate;
        it.pt_ch          = pt_ch;
        if (da_q_push(&it) < 0) free(copy);
        return cERR_DREAMAUDIO_NO_ERROR;
    }

    /* ----- PCM path: validate header, copy, enqueue ----- */
    if (!out->extradata || out->extralen != sizeof(pcmPrivateData_t)) {
        DA_DBG("write: missing/invalid pcmPrivateData (extralen=%u expected=%zu) — "
               "codec wasn't forced through software decode?",
               out->extralen, sizeof(pcmPrivateData_t));
        return cERR_DREAMAUDIO_ERROR;
    }

    pcmPrivateData_t *pcm = (pcmPrivateData_t *)out->extradata;
    unsigned int rate     = (unsigned int)pcm->sample_rate;
    unsigned int channels = (unsigned int)pcm->channels;
    if (rate == 0 || channels == 0 || channels > 8) {
        DA_DBG("write: bad pcm header rate=%u ch=%u", rate, channels);
        return cERR_DREAMAUDIO_ERROR;
    }

    uint8_t *copy = (uint8_t *)malloc(out->len);
    if (!copy) return cERR_DREAMAUDIO_ERROR;
    memcpy(copy, out->data, out->len);

    da_qitem_t it = {0};
    it.data     = copy;
    it.size     = out->len;
    it.pts_90k  = pts_90k;
    it.rate     = rate;
    it.channels = channels;
    if (da_q_push(&it) < 0) free(copy);
    return cERR_DREAMAUDIO_NO_ERROR;
}

/* ----- Command dispatcher --------------------------------------------- */

static int DreamAudioCommand(void *_context, OutputCmd_t cmd, void *arg)
{
    Context_t *context = (Context_t *)_context;

    switch (cmd) {
    case OUTPUT_OPEN:       return DreamAudioOpen(context, (char *)arg);
    case OUTPUT_CLOSE:      return DreamAudioClose(context, (char *)arg);
    case OUTPUT_PLAY:       return DreamAudioPlay(context, (char *)arg);
    case OUTPUT_STOP:       return DreamAudioStop(context, (char *)arg);
    case OUTPUT_FLUSH:      return DreamAudioFlush(context, (char *)arg);
    case OUTPUT_PAUSE:      return DreamAudioPause(context, (char *)arg);
    case OUTPUT_CONTINUE:   return DreamAudioContinue(context, (char *)arg);
    case OUTPUT_CLEAR:      return DreamAudioClear(context, (char *)arg);
    case OUTPUT_SWITCH:     return DreamAudioSwitch(context, (char *)arg);
    case OUTPUT_PTS:        return DreamAudioPts(context, (unsigned long long *)arg);
    case OUTPUT_AVSYNC:
    case OUTPUT_AUDIOMUTE:
    case OUTPUT_FASTFORWARD:
    case OUTPUT_REVERSE:
    case OUTPUT_DISCONTINUITY_REVERSE:
    case OUTPUT_SLOWMOTION:
    case OUTPUT_GET_FRAME_COUNT:
    case OUTPUT_GET_PROGRESSIVE:
    case OUTPUT_SET_BUFFER_SIZE:
    case OUTPUT_GET_BUFFER_SIZE:
        /* video-side or stub-for-audio — silent no-op */
        return cERR_DREAMAUDIO_NO_ERROR;
    default:
        DA_DBG("unhandled cmd %d", cmd);
        return cERR_DREAMAUDIO_NO_ERROR;
    }
}

/* ----- Output_t binding ------------------------------------------------ */

static char *DreamAudioCapabilities[] = { "audio", NULL };

struct Output_s DreamAudioOutput = {
    "DreamAudio",
    &DreamAudioCommand,
    &DreamAudioWrite,
    DreamAudioCapabilities
};
