-- Prove2me | Definitions.Def_SourceProof_fa85a2801ff0bffcd023f5a0
-- name    : SourceProof_fa85a2801ff0bffcd023f5a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:15.148904+00:00
-- url     : https://prove2.me/theorems/8449bceb-1140-4573-9965-9437101cef19
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_enorm_increment_le

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous paths of bounded variation have zero increment quadratic variation -/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology BigOperators

namespace StochLean

variable {T : ℝ≥0}

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_fa85a2801ff0bffcd023f5a0 (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    (∑ i, ENNReal.ofReal |π.increment f i|) ≤ eVariationOn f (Icc 0 T) := by
  let u : ℕ → ℝ≥0 := fun n ↦ π.point ⟨min n π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hu : Monotone u := fun n m hnm ↦ π.monotone_point (by
    change min n π.size ≤ min m π.size
    exact min_le_min_right _ hnm)
  have hmem : ∀ n, u n ∈ Icc 0 T := fun n ↦ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _⟩
  have hsum := eVariationOn.sum_le (n := π.size) (f := f) hu hmem
  rw [Finset.sum_range] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  have h₀ : u i = π.left i := by
    simp only [u, StochLean.TimePartition.left, min_eq_left i.isLt.le]
    exact congrArg π.point (Fin.ext rfl)
  have h₁ : u (i + 1) = π.right i := by
    simp only [u, StochLean.TimePartition.right, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    exact congrArg π.point (Fin.ext rfl)
  rw [h₀, h₁, edist_dist, Real.dist_eq, StochLean.TimePartition.increment]
end TimePartition

end StochLean


