-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.flipSet_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:19.746276+00:00
-- url     : https://prove2.me/submissions/7e842922-44fa-4172-8647-92d13e717576

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_diffSet
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x w : Cube ι) : flipSet x (diffSet x w) = w := by
  funext i
  rw [flipSet_apply]
  by_cases h : x i = w i
  · have hi : i ∉ diffSet x w := fun hh => (mem_diffSet.mp hh) h
    rw [if_neg hi, h]
  · have hi : i ∈ diffSet x w := mem_diffSet.mpr h
    rw [if_pos hi]
    revert h
    cases x i <;> cases w i <;> simp
end AaronsonAmbainis.DetBij
