-- Prove2me | solution 1 for Aggmetrics.DataStream.precision_depends_on_prior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:39.017747+00:00
-- url     : https://prove2.me/submissions/872db65d-f56d-41ec-98ed-ac393bce9362

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution :
    precision (17 / 20) (17 / 20) (1 / 2) = 17 / 20 ∧
    precision (17 / 20) (17 / 20) (1 / 20) = 17 / 74 ∧
    precision (17 / 20) (17 / 20) (1 / 2) ≠ precision (17 / 20) (17 / 20) (1 / 20) := by
  unfold precision
  refine ⟨by norm_num, by norm_num, by norm_num⟩
end Aggmetrics.DataStream
