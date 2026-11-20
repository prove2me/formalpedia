-- Prove2me | solution 1 for Aggmetrics.DataStream.cell_ratio_prior_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:55:30.439729+00:00
-- url     : https://prove2.me/submissions/95ed03ef-9219-46ea-ad54-5791e7ca3987

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (prior rate : ℝ) (hprior : prior ≠ 0) :
    (prior * rate) / (prior * rate + prior * (1 - rate)) = rate := by
  have hsum : prior * rate + prior * (1 - rate) = prior := by ring
  rw [hsum, mul_comm, mul_div_assoc, div_self hprior, mul_one]
end Aggmetrics.DataStream
