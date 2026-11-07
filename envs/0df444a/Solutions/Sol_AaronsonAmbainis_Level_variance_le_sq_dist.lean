-- Prove2me | solution 1 for AaronsonAmbainis.Level.variance_le_sq_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:26.180876+00:00
-- url     : https://prove2.me/submissions/a15a79fc-0ae7-4e82-8d47-b536deaeba8a

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_sum_sub_mean

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (c : ℝ) :
    variance f ≤ (∑ x, (f x - c) ^ 2) / 2 ^ Fintype.card ι := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h1 : ∑ x, (f x - c) ^ 2
      = ∑ x, (f x - mean f) ^ 2 + 2 * (mean f - c) * ∑ x, (f x - mean f)
        + ∑ _x : Cube ι, (mean f - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have h2 : 0 ≤ ∑ _x : Cube ι, (mean f - c) ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  unfold variance
  refine div_le_div_of_nonneg_right ?_ hpos.le
  rw [h1, sum_sub_mean, mul_zero, add_zero]
  exact le_add_of_nonneg_right h2
end AaronsonAmbainis.Level
