-- Prove2me | Definitions.Def_RiemannMasullo_DirectSumSeminorm
-- name    : RiemannMasullo_DirectSumSeminorm
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:24:33.952047+00:00
-- url     : https://prove2.me/theorems/fee9e9bf-3f89-432f-b7d7-06c78e87d7da
-- title:
--   Sum of coordinate seminorms on an algebraic direct sum
-- statement:
--   Given a seminorm on each summand over a normed field, the direct-sum seminorm of a finitely supported vector is the sum of the seminorms of its coordinates. The triangle inequality follows by summing over the union of two supports. Absolute homogeneity follows from that of each coordinate seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L15-L25

import Mathlib

noncomputable section
open scoped DirectSum

namespace RiemannMasullo

variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

/-- The sum of the coordinate seminorms on a direct sum, evaluated using finite support. -/
def directSumSeminorm (p : ∀ i, Seminorm 𝕜 (X i)) : Seminorm 𝕜 (⨁ i, X i) := by
  refine Seminorm.of (fun x ↦ x.sum fun i ↦ p i) (fun x y ↦ ?_) (fun a x ↦ ?_)
  · rw [DFinsupp.sum_of_support_subset DFinsupp.support_add (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_left (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_right (fun i _ ↦ map_zero (p i)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦ map_add_le_add (p i) (x i) (y i)
  · rw [DFinsupp.sum_of_support_subset (DFinsupp.support_smul a x) (fun i _ ↦ map_zero (p i))]
    simp only [DFinsupp.smul_apply, map_smul_eq_mul, Finset.mul_sum, DFinsupp.sum]

end RiemannMasullo


