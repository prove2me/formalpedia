-- Prove2me | solution 1 for AaronsonAmbainis.Row.abs_multilinear_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:14:42.447819+00:00
-- url     : https://prove2.me/submissions/5d644864-6020-469e-9f28-4b4448edf1c7

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
import Theorems.Thm_AaronsonAmbainis_Row_weight_nonneg
import Theorems.Thm_AaronsonAmbainis_Row_sum_weight_mul_chi
import Theorems.Thm_AaronsonAmbainis_Row_sum_weight

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Row
theorem _root_.solution (a : Finset ι → ℝ)
    (h : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    |∑ T, a T * ∏ i ∈ T, u i| ≤ 1 := by
  have key : ∑ T, a T * ∏ i ∈ T, u i = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
    calc ∑ T, a T * ∏ i ∈ T, u i
        = ∑ T, a T * ∑ z : Cube ι, weight u z * chi T z := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [sum_weight_mul_chi]
      _ = ∑ T, ∑ z : Cube ι, weight u z * (a T * chi T z) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          ring
      _ = ∑ z : Cube ι, ∑ T, weight u z * (a T * chi T z) := Finset.sum_comm
      _ = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [Finset.mul_sum]
  rw [key]
  calc |∑ z : Cube ι, weight u z * ∑ T, a T * chi T z|
      ≤ ∑ z : Cube ι, |weight u z * ∑ T, a T * chi T z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : Cube ι, weight u z := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (weight_nonneg u hu z)]
        exact mul_le_of_le_one_right (weight_nonneg u hu z) (h z)
    _ = 1 := sum_weight u
end AaronsonAmbainis.Row
