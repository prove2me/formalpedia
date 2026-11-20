-- Prove2me | solution 1 for Aggmetrics.DataStream.recall_prior_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:40.096432+00:00
-- url     : https://prove2.me/submissions/9f2c559a-39bf-4b43-92cb-4c9112be9e47

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
import Theorems.Thm_Aggmetrics_DataStream_cell_ratio_prior_invariant

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (prior r : ℝ) (hprior : prior ≠ 0) :
    (prior * r) / (prior * r + prior * (1 - r)) = r :=
  cell_ratio_prior_invariant prior r hprior
end Aggmetrics.DataStream
