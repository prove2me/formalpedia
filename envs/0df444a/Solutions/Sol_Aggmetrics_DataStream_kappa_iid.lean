-- Prove2me | solution 1 for Aggmetrics.DataStream.kappa_iid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:07.762477+00:00
-- url     : https://prove2.me/submissions/563521ca-69e7-43b1-ae79-b73a8c9c7113

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α : ℝ) :
    kappaVar (fun d => if d = 0 then 1 else 0) α = (1 - α) / (1 + α) := by
  unfold kappaVar kappaFactor
  simp
end Aggmetrics.DataStream
