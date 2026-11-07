-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mean_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:32.934203+00:00
-- url     : https://prove2.me/submissions/2bf589b6-5304-4c58-bbb5-428ff33f0706

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (a b : ℝ) (g : Cube ι → ℝ) :
    mean (fun x => a + b * g x) = a + b * mean g := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  simp only [mean]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube,
    ← Finset.mul_sum, add_div, mul_div_cancel_left₀ a hne, mul_div_assoc]
end AaronsonAmbainis.Bridge
