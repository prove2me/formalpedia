-- Prove2me | Definitions.Def_SourceProof_5c3ed2d682980800c53cd4ac
-- name    : SourceProof_5c3ed2d682980800c53cd4ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:08.757401+00:00
-- url     : https://prove2.me/theorems/2c8ab7e4-ba2c-41e7-9807-9ac815699717
-- title:
--   StochLean source theorem: StochLean.TimePartition.taggedStep_eq_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
import Definitions.Def_SourceProof_0d9d0191109103cc7be46cb1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arbitrarily tagged step approximations

Tags may be either endpoint or any point between. They need not be ordered
separately from their containing cells; repeated partition endpoints are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_5c3ed2d682980800c53cd4ac (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : π.taggedStep ξ f t = f (ξ i) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [StochLean.TimePartition.taggedStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi (fun _ ↦ f (ξ i))
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji ((_root_.Prove2MeSourceProof.h_0d9d0191109103cc7be46cb1 π) hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
end StochLean.TimePartition


