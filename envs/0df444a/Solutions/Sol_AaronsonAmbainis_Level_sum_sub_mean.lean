-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_sub_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:55.612218+00:00
-- url     : https://prove2.me/submissions/0e2a348e-e601-4f32-a350-f9d9a74e8036

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_sum_const_cube

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) : ∑ x, (f x - mean f) = 0 := by
  rw [Finset.sum_sub_distrib, sum_const_cube]
  unfold mean
  rw [mul_div_cancel₀ _ (by positivity), sub_self]
end AaronsonAmbainis.Level
