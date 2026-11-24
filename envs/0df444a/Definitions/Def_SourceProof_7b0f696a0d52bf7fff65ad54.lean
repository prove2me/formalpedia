-- Prove2me | Definitions.Def_SourceProof_7b0f696a0d52bf7fff65ad54
-- name    : SourceProof_7b0f696a0d52bf7fff65ad54
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:23.769723+00:00
-- url     : https://prove2.me/theorems/cea951ff-5a68-4135-9a56-90ce3b009b01
-- title:
--   StochLean source theorem: StochLean.TimePartition.frechet_taylor_sum_with_remainder

import Definitions.Def_StochLean_Analysis_PathVariation_VectorTaylorSums_F000
import Definitions.Def_SourceProof_0a3c16aaf9407b6acdc7ca51
import Definitions.Def_SourceProof_deb465799a9f476945dd8c4f
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact Frechet Taylor sums with partial terminal cells

Derivatives are sampled at the original left endpoint. After the evaluation
time, zero increments remove their contributions without moving the sample.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : ℝ≥0}

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_7b0f696a0d52bf7fff65ad54 (π : TimePartition S)
    (f : E → ℝ) (x : ℝ≥0 → E) (t : ℝ≥0) :
    f (x (min S t)) - f (x 0) =
      (∑ i : Fin π.size, fderiv ℝ f (x (π.left i))
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      (1 / 2 : ℝ) * (∑ i : Fin π.size, fderiv ℝ (fderiv ℝ f) (x (π.left i))
        (x (min (π.right i) t) - x (min (π.left i) t))
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      frechetTaylorErrorSum π f x t := by
  have ht : (∑ i : Fin π.size,
      (f (x (min (π.right i) t)) - f (x (min (π.left i) t)))) =
      f (x (min S t)) - f (x 0) := by
    simpa only [StochLean.TimePartition.increment, zero_min] using
      (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 π) (fun u ↦ f (x (min u t)))
  rw [← ht, StochLean.frechetTaylorErrorSum, StochLean.normSquarePairSum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [_root_.Prove2MeSourceProof.h_deb465799a9f476945dd8c4f]
  by_cases hi : π.left i ≤ t
  · rw [min_eq_left hi, StochLean.frechetSecondOrderRemainder]
    ring
  · have hl : t ≤ π.left i := (lt_of_not_ge hi).le
    have hr : t ≤ π.right i := hl.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
    simp only [min_eq_right hl, min_eq_right hr, sub_self, map_zero,
      mul_zero, add_zero, _root_.Prove2MeSourceProof.h_0a3c16aaf9407b6acdc7ca51]
end TimePartition

end StochLean


