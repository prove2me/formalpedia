-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.diffSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:16.58634+00:00
-- url     : https://prove2.me/submissions/030736d1-b14f-490a-99c1-fb1a34b4753f

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_diffSet
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  rw [mem_diffSet, flipSet_apply]
  by_cases h : i ∈ S <;> cases x i <;> simp [h]
end AaronsonAmbainis.DetBij
