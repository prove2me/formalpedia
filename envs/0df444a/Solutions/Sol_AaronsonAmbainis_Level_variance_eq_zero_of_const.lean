-- Prove2me | solution 1 for AaronsonAmbainis.Level.variance_eq_zero_of_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:55.041513+00:00
-- url     : https://prove2.me/submissions/d224bdd5-ffb3-4945-90bf-7527442e1825

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_sum_const_cube

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (h : ∀ x y, f x = f y) : variance f = 0 := by
  have hm : ∀ x, f x = mean f := by
    intro x
    unfold mean
    rw [Finset.sum_congr rfl (fun y _ => h y x), sum_const_cube,
      mul_div_cancel_left₀ _ (by positivity)]
  unfold variance
  rw [Finset.sum_eq_zero (fun x _ => by rw [hm x, sub_self]; norm_num), zero_div]
end AaronsonAmbainis.Level
