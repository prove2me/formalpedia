-- Prove2me | solution 1 for Aggmetrics.DataStream.tnorm_hard_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:59.110196+00:00
-- url     : https://prove2.me/submissions/c8b3be7b-481e-4d67-be24-f28283ead0c5

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    min (yt a) (if b = k then (1 : ℝ) else 0) = yt a * (if b = k then (1 : ℝ) else 0) := by
  by_cases h : b = k
  · simp [h, (hy a).2]
  · simp [h, (hy a).1]
end Aggmetrics.DataStream
