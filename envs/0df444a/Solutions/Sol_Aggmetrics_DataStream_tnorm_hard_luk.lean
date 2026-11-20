-- Prove2me | solution 1 for Aggmetrics.DataStream.tnorm_hard_luk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:59.727674+00:00
-- url     : https://prove2.me/submissions/e1935a1f-9640-477c-92e3-f363da6bd93e

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    max 0 (yt a + (if b = k then (1 : ℝ) else 0) - 1) = yt a * (if b = k then (1 : ℝ) else 0) := by
  by_cases h : b = k
  · simp [h, (hy a).1]
  · simp [h, (hy a).2]
end Aggmetrics.DataStream
