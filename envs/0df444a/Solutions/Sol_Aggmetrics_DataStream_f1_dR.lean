-- Prove2me | solution 1 for Aggmetrics.DataStream.f1_dR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:45.582403+00:00
-- url     : https://prove2.me/submissions/a365b366-9652-477c-95fb-44cd204385bf

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 y S π)
      (2 * π * (π + (1 - π) * (1 - S)) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) R := by
  have h := hasDerivAt_ratio_lin (2 * π) 0 π (π + (1 - π) * (1 - S)) R
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
