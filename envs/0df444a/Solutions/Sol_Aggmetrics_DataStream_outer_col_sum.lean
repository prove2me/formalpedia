-- Prove2me | solution 1 for Aggmetrics.DataStream.outer_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:56.00068+00:00
-- url     : https://prove2.me/submissions/5eb69bd5-63bc-4b48-a0a3-f9f5495d1188

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (yt p : Fin m → ℝ) (hy : ∑ a, yt a = 1) (b : Fin m) :
    ∑ a, outer yt p a b = p b := by
  simp [outer, ← Finset.sum_mul, hy]
end Aggmetrics.DataStream
