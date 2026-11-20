-- Prove2me | solution 1 for Aggmetrics.DataStream.outer_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:55.516609+00:00
-- url     : https://prove2.me/submissions/2331e85f-7cba-49ff-8910-a74e4da5621d

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (yt p : Fin m → ℝ) (hp : ∑ b, p b = 1) (a : Fin m) :
    ∑ b, outer yt p a b = yt a := by
  simp [outer, ← Finset.mul_sum, hp]
end Aggmetrics.DataStream
