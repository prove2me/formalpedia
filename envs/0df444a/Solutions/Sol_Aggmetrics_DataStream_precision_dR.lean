-- Prove2me | solution 1 for Aggmetrics.DataStream.precision_dR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:18.335756+00:00
-- url     : https://prove2.me/submissions/4e69b31b-dc63-4c3a-b556-bbd723e0ffe1

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision y S π)
      (π * (1 - π) * (1 - S) / (π * R + (1 - π) * (1 - S)) ^ 2) R := by
  have h := hasDerivAt_ratio_lin π 0 π ((1 - π) * (1 - S)) R (π * R + (1 - π) * (1 - S))
    (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
