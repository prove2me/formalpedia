-- Prove2me | solution 1 for AaronsonAmbainis.Level.inflR_eq_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:00.195169+00:00
-- url     : https://prove2.me/submissions/be0120e4-78ea-44f3-8b88-3db9d5a0aec1

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (j : ι) :
    inflR f j = (∑ x, (f x - f (flipSet x {j})) ^ 2) / 2 ^ Fintype.card ι / 4 := by
  have h : ∀ x : Cube ι,
      ((f x - f (flipSet x {j})) / 2) ^ 2 = (f x - f (flipSet x {j})) ^ 2 / 4 :=
    fun x => by ring
  simp only [inflR, h]
  rw [← Finset.sum_div, div_right_comm]
end AaronsonAmbainis.Level
