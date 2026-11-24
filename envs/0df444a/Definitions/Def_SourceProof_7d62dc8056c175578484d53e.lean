-- Prove2me | Definitions.Def_SourceProof_7d62dc8056c175578484d53e
-- name    : SourceProof_7d62dc8056c175578484d53e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:01.304122+00:00
-- url     : https://prove2.me/theorems/e005c74d-37e5-4be1-a704-eba414d0a2a8
-- title:
--   StochLean source theorem: StochLean.TimePartition.leftStep_eq_zero_of_horizon_lt

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-step bounds and approximation with varying horizons

Sampling uses only past values, including the initial value. Compact-uniform
approximation of a continuous function therefore needs eventual horizon coverage
and vanishing mesh, not nested partitions or a deterministic mesh rate.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_7d62dc8056c175578484d53e (π : TimePartition T) (f : ℝ≥0 → ℝ)
    {t : ℝ≥0} (ht : T < t) : π.leftStep f t = 0 := by
  classical
  have ht0 : t ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ T from bot_le).trans_lt ht)
  rw [StochLean.TimePartition.leftStep, if_neg ht0]
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact not_le_of_gt ht (hi.2.trans ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _))
end StochLean.TimePartition


