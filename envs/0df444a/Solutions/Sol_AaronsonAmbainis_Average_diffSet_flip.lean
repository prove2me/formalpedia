-- Prove2me | solution 1 for AaronsonAmbainis.Average.diffSet_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:39:08.278193+00:00
-- url     : https://prove2.me/submissions/46de0f34-fda8-4f0b-8848-41f720323b24

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_flipSet_apply
import Theorems.Thm_AaronsonAmbainis_mem_diffSet


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (x y : Cube ι) (S : Finset ι) :
    diffSet (flipSet x S) (flipSet y S) = diffSet x y := by
  ext i
  rw [mem_diffSet, mem_diffSet, flipSet_apply, flipSet_apply]
  by_cases hS : i ∈ S
  · rw [if_pos hS, if_pos hS]
    cases x i <;> cases y i <;> simp
  · rw [if_neg hS, if_neg hS]
end AaronsonAmbainis.Average
