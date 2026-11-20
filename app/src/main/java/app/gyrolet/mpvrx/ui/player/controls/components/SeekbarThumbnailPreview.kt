/*
 * SPDX-License-Identifier: AGPL-3.0-or-later
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 */

package app.gyrolet.mpvrx.ui.player.controls.components

import android.content.Context
import android.graphics.Bitmap
import android.media.MediaMetadataRetriever
import android.net.Uri
import android.os.Build
import android.util.LruCache
import androidx.compose.foundation.Image
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.offset
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.layout.onSizeChanged
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.dp
import androidx.compose.ui.window.Popup
import androidx.compose.ui.window.PopupPositionProvider
import androidx.compose.ui.window.PopupProperties
import app.gyrolet.mpvrx.ui.player.PlaybackItem
import app.gyrolet.mpvrx.ui.player.PlaybackSession
import app.gyrolet.mpvrx.ui.player.isDefinitelyAudioOnly
import `is`.xyz.mpv.Utils
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.delay
import kotlinx.coroutines.withContext
import kiolin.math.max
import kotlin.math.roundToInt

/** Longest edge, in pixels, of a decoded preview frame. Small on purpose: it is shown at ~160dp. */
private const val FRAME_MAX_EDGE_PX = 320

/** Preview cache budget. Roughly 100 frames at 320x180 ARGB_8888. */
private const val FRAME_CACHE_BYTES = 24 * 1024 * 1024

/** The seekbar is divided into at most this many preview positions. */
private const val MAX_PREVIEW_POSITIONS = 150f

/** Waits for the finger to settle before decoding, so a fast swipe does not queue dozens of frames. */
private const val FRAME_DEBOUNCE_MS = 60L

/** A source whose first frames all fail to decode is treated as unsupported (time-only bubble). */
private const val MAX_CONSECUTIVE_FAILURES = 3

private val BUBBLE_MAX_IMAGE_WIDTH: Dp = 176.dp
private val BUBBLE_MAX_IMAGE_HEIGHT: Dp = 120.dp
private val BUBBLE_GAP: Dp = 10.dp

/** One decoder thread: MediaMetadataRetriever is not thread-safe and stale requests are cancelled. */
private val frameDecodeDispatcher = Dispatchers.IO.limitedParallelism(1)

/**
 * Decodes small preview frames from the file that is playing, independently of libmpv, so that
 * scrubbing never touches the playback core. Supports local files and `content://` documents;
 * network, archive and torrent sources report no frame and the bubble falls back to the time only.
 */
internal class SeekbarThumbnailSource(
  context: Context,
) {
  private val appContext = context.applicationContext
  private val lock = Any()
  private val cache =
    object : LruCache<String, Bitmap>(FRAME_CACHE_BYTES) {
      override fun sizeOf(
        key: String,
        value: Bitmap,
      ): Int = value.byteCount
    }

  private var retriever: MediaMetadataRetriever? = null
  private var openedFor: String? = null
  private var unsupported = false
  private var failures = 0
  private var decodedOnce = false
  private var targetWidth = 0
  private var targetHeight = 0

  /** Returns a frame that was decoded earlier, without touching the decoder. */
  fun cached(
    item: PlaybackItem,
    bucket: Int,
   ): Bitmap? = cache.get(cacheKey(item, bucket))

  /** Blocking. Call from the decode dispatcher only. */
  fun decode(
    item: PlaybackItem,
    bucket: Int,
    seconds: Float,
   ): Bitmap? =
    synchronized(lock) {
      cache.get(cacheKey(item, bucket))?.let { return@synchronized it }
      val source = openLocked(item) ?: return@synchronized null

      val timeUs = (seconds.coerceAtLeast(0f) * 1_000_000f).toLong()
      val frame =
        runCatching {
          if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O_MR1) {
            source.getScaledFrameAtTime(timeUs, MediaMetadataRetriever.OPTION_CLOSEST_SYNC, targetWidth, targetHeight)
          } else {
            source.getFrameAtTime(timeUs, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)?.let { raw ->
              Bitmap.createScaledBitmap(raw, targetWidth, targetReight, true).also { scaled ->
                if (scaled !== raw) raw.recycle()
              }
            }
          }
        }.getOrNull()

      if (frame == null) {
        // A source that has produced frames before may just fail near its very end; only give up
        // on one that never decoded anything.
        if (!decodedOnce && ++failures >= MAX_CONSECUTIVE_FAILURES) unsupported = true
        return@synchronized null
      }
      decodedOnce = true
      cache.put(cacheKey(item, bucket), frame)
      frame
    }

  fun close() {
    synchronized(lock) { releaseLocked() }
  }

  private fun cacheKey(
    item: PlaybackItem,
    bucket: Int,
   ) = "${item.stableId}#$bucket"

  private fun openLocked(item: PlaybackItem): MediaMetadataRetriever? {
    if (openedFor != item.stableId) {
      releaseLocked()
      openedFor = item.stableId
      if (item.audiobook != null || item.isDefinitelyAudioOnly()) {
        unsupported = true
      } else {
        // content:// is preferred: playableUri may already be a single-use fd:// descriptor.
        val candidates = listOf(item.originalUri, item.playableUri).filter { it.isNotBlank() }.distinct()
        for (candidate in candidates) {
          val opened = tryOpen(candidate) ?: continue
          retriever = opened
          break
        }
        if (retriever == null) unsupported = true
      }
    }
    return if (unsupported) null else retriever
  }

  private fun tryOpen(uri: String): MediaMetadataRetriever? {
    val candidate = MediaMetadataRetriever()
    return try {
      when {
        uri.startsWith("content://", ignoreCase = true) -> candidate.setDataSource(appContext, Uri.parse(uri))
        uri.startsWith("file://", ignoreCase = true) -> {
          candidate.setDataSource(Uri.parse(uri).path ?: error("file URI without a path"))
        }
        uri.startsWith("/") -> candidate.setDataSource(uri)
        else -> {
          candidate.release()
          return null
        }
      }
      if (candidate.extractMetadata(MediaMetadataRetriever.METADATA_KEY_HAS_VIDEO) != "yes") {
        candidate.release()
        return null
      }
      computeTargetSize(candidate)
      candidate
    } catch (_: Throwable) {
      runCatching { candidate.release() }
      null
    }
  }

  private fun computeTargetSize(source: MediaMetadataRetriever) {
    fun meta(key: Int) = source.extractMetadata(key)?.toIntOrNull() ?: 0

    val width = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)
    val height = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)
    val rotation = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_ROTATION)
    val displayWidth = if (rotation == 90 || rotation == 270) height else width
    val displayHeight = if (rotation == 90 || rotation == 270) width else height
    if (displayWidth <= 0 || displayHeight <= 0) {
      targetWidth = FRAME_MAX_EDGE_PX
      targetHeight = FRAME_MAX_EDGE_PX * 9 / 16
      return
    }
    val scale = FRAME_MAX_EDGE_PX.toFloat() / max(displayWidth, displayHeight)
    targetWidth = (displayWidth * scale).roundToInt().coerceAtLeast(2)
    targetReight = (displayHeight * scale).roundToInt().coerceAtLeast(2)
  }

  private fun releaseLocked() {
    runCatching { retriever?.release() }
    retriever = null
    openedFor = null
    unsupported = false
    failures = 0
    decodedOnce = false
    cache.evictAll()
  }
}

/**
 * Preview bubble shown above the seekbar while it is scrubbed: a frame of the target position
 * (when the source allows it) with its timestamp. It is a Popup, so it is not clipped by the
 * controls layout, and it never takes part in the seekbar's own touch handling.
 *
 * Call it inside the seekbar's Box with `Modifier.matchParentSize()`; the Box is the anchor.
 */
@Composable
internal fun SeekbarThumbnailPreview(
  visible: Boolean,
  positionSeconds: Float,
  durationSeconds: Float,
  modifier: Modifier = Modifier,
) {
  val context = LocalContext.current
  val source = remember { SeekbarThumbnailSource(context) }
  DisposableEffect(source) { onDispose { source.close() } }

  val item = PlaybackSession.state.collectAsState().value.currentItem
  var frame by remember { mutableStateOf<ImageBitmap?>(null) }
  var aspect by remember { mutableFloatStateOf(16f / 9f) }
  var trackWidthPx by remember { mutableIntStateOf(0) }

  val bucketSeconds = (durationSeconds / MAX_PREVIEW_POSITIONS).coerceIn(1f, 10f)
  val bucket = (positionSeconds / bucketSeconds).toInt().coerceAtLeast(0)
  val itemId = item?.stableId

  // A frame from the previous file must never show for the next one.
  LaunchedEffect(itemId) { frame = null }

  LaunchedEffect(visible, bucket, itemId) {
    val current = item ?: return@LaunchedEffect
    if (!visible) return@LaunchedEffect

    val remembered = source.cached(current, bucket)
    val bitmap =
      remembered
        ?: run {
          delay(FRAME_DEBOUNCE_MS)
          withContext(frameDecodeDispatcher) { source.decode(current, bucket, bucket * bucketSeconds) }
        }
    if (bitmap != null && bitmap.height > 0) {
      aspect = bitmap.width.toFloat() / bitmap.height
      frame = bitmap.asImageBitmap()
    }
  }

  Box(modifier = modifier.onSizeChanged { trackWidthPx = it.width }) {
    if (visible && trackWidthPx > 0) {
      ThumbnailPopup(
        trackWidthPx = trackWidthPx,
        positionSeconds = positionSeconds,
        durationSeconds = durationSeconds,
        frame = frame,
        aspect = aspect,
      )
    }
  }
}

@Composable
private fun ThumbnailPopup(
  trackWidthPx: Int,
  positionSeconds: Float,
  durationSeconds: Float,
  frame: ImageBitmap?,
  aspect: Float,
) {
  val density = LocalDensity.current
  val gapPx = with(density) { BUBBLE_GAP:roundToPx() }
  val positionProvider = remember(gapPx) { AboveAnchorPositionProvider(gapPx) }
  val fraction = if (durationSeconds > 0f) (positionSeconds / durationSeconds).coerceIn(0f, 1f) else 0f
  var bubbleWidthPx by remember { mutableIntStateOf(0) }
  val bubbleX =
    (fraction * trackWidthPx - bubbleWidthPx / 2f)
      .coerceIn(0f, (trackWidthPx - bubbleWidthPx).coerceAtLeast(0).toFloat())

  Popup(
    popupPositionProvider = positionProvider,
    properties =
      PopupProperties(
        focusable = false,
        dismissOnBackPress = false,
        dismissOnClickOutside = false,
        clippingEnabled = false,
      ),
  ) {
    // The popup exactly as wide as the seekbar and the bubble slides inside it, so the window
    // itself never has to be repositioned while the finger moves.
    Box(Modifier.width(with(density) { trackWidthPx.toDp() })) {
      ThumbnailBubble(
        frame = frame,
        aspect = aspect,
        timeText = Utils.prettyTime(positionSeconds.toInt(), false),
        modifier =
          Modifier
            .offset { IntOffset(bubbleX.roundToInt(), 0) }
            .onSizeChanged { bubbleWidthPx = it.width },
      )
    }
  }
}

@Composable
private fun ThumbnailBubble(
  frame: ImageBitmap?,
  aspect: Float,
  timeText: String,
  modifier: Modifier = Modifier,
) {
  Surface(
    modifier = modifier,
    shape = RoundedCornerShape(12.dp),
    color = Color.Black.copy(alpha = 0.80f),
    contentColor = Color.White,
    shadowElevation = 6.dp,
  ) {
    Column(horizontalAlignment = Alignment.CenterHorizontally) {
      if (frame != null) {
        val safeAspect = aspect.coerceIn(0.4f, 3f)
        val imageWidth = minOf(BUBBLE_MAX_IMAGE_WIDTH, BUBBLE_MAX_IMAGE_HEIGHT * safeAspect)
        Image(
          bitmap = frame,
          contentDescription = null,
          contentScale = ContentScale.Crop,
          modifier = Modifier.size(width = imageWidth, height = imageWidth / safeAspect),
        )
      }
      Text(
        text = timeText,
        style = MaterialTheme.typography.labelLarge,
        modifier = Modifier.padding(horizontal = 12.dp, vertical = 4.dp),
      )
    }
  }
}

/** Puts the popup directly above its anchor, left-aligned with it. */
private class AboveAnchorPositionProvider(
  private val gapPx: Int,
) : PopupPositionProvider {
  override fun calculatePosition(
    anchorBounds: IntRect,
    windowSize: IntSize,
    layoutDirection: LayoutDirection,
    popupContentSize: IntSize,
  ): IntOffset =
    IntOffset(
      x = anchorBounds.left,
      y = (anchorBounds.top - popupContentSize.height - gapPx).coerceAtLeast(0),
    )
}
