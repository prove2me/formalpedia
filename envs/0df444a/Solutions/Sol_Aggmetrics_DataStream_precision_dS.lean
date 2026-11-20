-- Prove2me | solution 1 for Aggmetrics.DataStream.precision_dS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:21.366976+00:00
-- url     : https://prove2.me/submissions/f01c2bef-879a-4b76-886b-2d36f6b9fdb9

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision R y π)
      (π * (1 - π) * R / (π * R + (1 - π) * (1 - S)) ^ 2) S := by
  have h := hasDerivAt_ratio_lin 0 (π * R) (-(1 - π)) (π * R + (1 - π)) S
    (π * R + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
