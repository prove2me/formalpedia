-- Prove2me | Definitions.Def_SourceProof_1414dbb134d20c88dc05607c
-- name    : SourceProof_1414dbb134d20c88dc05607c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:49.466747+00:00
-- url     : https://prove2.me/theorems/ba858506-c637-4b83-879b-4b6fd28528dd
-- title:
--   StochLean source theorem: StochLean.TimePartition.taylor_sum_with_remainder

import Definitions.Def_StochLean_Analysis_PathVariation_TaylorSums_F000
import Definitions.Def_SourceProof_62c74d4c6782b2a3e76047aa
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact second-order Taylor sums with retained partial cells -/

@[expose] public section

open Set Filter Finset
open scoped NNReal Topology

namespace StochLean

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_1414dbb134d20c88dc05607c {S : ℝ≥0} (π : TimePartition S)
    (f : ℝ → ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    f (x (min S t)) - f (x 0) =
      (∑ i : Fin π.size, deriv f (x (π.left i)) *
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      (1 / 2 : ℝ) * (∑ i : Fin π.size, deriv (deriv f) (x (π.left i)) *
        (x (min (π.right i) t) - x (min (π.left i) t)) ^ 2) +
      quadraticTaylorErrorSum π f x t := by
  have ht : (∑ i : Fin π.size,
      (f (x (min (π.right i) t)) - f (x (min (π.left i) t)))) =
      f (x (min S t)) - f (x 0) := by
    simpa only [StochLean.TimePartition.increment, zero_min] using
      (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 π) (fun u ↦ f (x (min u t)))
  rw [← ht, StochLean.quadraticTaylorErrorSum, StochLean.quadraticPairSum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : π.left i ≤ t
  · rw [min_eq_left hi]
    have h := _root_.Prove2MeSourceProof.h_62c74d4c6782b2a3e76047aa f (x (π.left i)) (x (min (π.right i) t))
    linear_combination -h
  · have hl : t ≤ π.left i := (lt_of_not_ge hi).le
    have hr : t ≤ π.right i := hl.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
    simp only [min_eq_right hl, min_eq_right hr, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero]
end TimePartition

end StochLean


