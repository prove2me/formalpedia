-- Prove2me | Definitions.Def_SourceProof_1f1a39edad68d4f3bc6e94ca
-- name    : SourceProof_1f1a39edad68d4f3bc6e94ca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:31.360802+00:00
-- url     : https://prove2.me/theorems/ff83f3a5-f127-4b21-89e4-1fed92eeccd3
-- title:
--   StochLean source theorem: StochLean.TimePartition.leftStep_eq_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_SourceProof_0d9d0191109103cc7be46cb1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca (π : TimePartition T) (f : ℝ≥0 → ℝ) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) : π.leftStep f t = f (π.left i) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [StochLean.TimePartition.leftStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi (fun _ ↦ f (π.left i))
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji ((_root_.Prove2MeSourceProof.h_0d9d0191109103cc7be46cb1 π) hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
end StochLean.TimePartition


