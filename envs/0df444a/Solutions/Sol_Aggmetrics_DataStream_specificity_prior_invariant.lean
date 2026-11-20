-- Prove2me | solution 1 for Aggmetrics.DataStream.specificity_prior_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:43.904826+00:00
-- url     : https://prove2.me/submissions/d41040a0-48d3-4e80-806c-d4048a6a9e27

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
import Theorems.Thm_Aggmetrics_DataStream_cell_ratio_prior_invariant

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (prior specificity : ℝ) (hprior : prior ≠ 1) :
    ((1 - prior) * specificity) / ((1 - prior) * specificity + (1 - prior) * (1 - specificity))
      = specificity :=
  cell_ratio_prior_invariant (1 - prior) specificity (sub_ne_zero.mpr (Ne.symm hprior))
end Aggmetrics.DataStream
