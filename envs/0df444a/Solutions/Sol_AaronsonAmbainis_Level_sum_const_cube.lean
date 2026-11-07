-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_const_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:12.698983+00:00
-- url     : https://prove2.me/submissions/0f8a3144-83e3-436b-8f13-d155c1b4b65b

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (c : ℝ) : ∑ _x : Cube ι, c = 2 ^ Fintype.card ι * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
end AaronsonAmbainis.Level
