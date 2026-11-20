-- Prove2me | solution 1 for Aggmetrics.DataStream.f1_dS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:48.333335+00:00
-- url     : https://prove2.me/submissions/0b222615-10b3-477f-bc87-2dbc08d294b3

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R y π)
      (2 * π * (1 - π) * R / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) S := by
  have h := hasDerivAt_ratio_lin 0 (2 * π * R) (-(1 - π)) (π * (1 + R) + (1 - π)) S
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
