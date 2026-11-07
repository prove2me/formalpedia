-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.flipSet_antipode_agSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:26.736929+00:00
-- url     : https://prove2.me/submissions/8f1bf506-5747-4110-9635-dd58bc5201b7

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Theorems.Thm_AaronsonAmbainis_DetBij_mem_agSet
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (u z : Cube ι) : flipSet (antipode u) (agSet u z) = z := by
  funext i
  rw [flipSet_apply]
  by_cases h : u i = z i
  · rw [if_pos (mem_agSet.mpr h)]
    simp [antipode, h]
  · rw [if_neg (fun hh => h (mem_agSet.mp hh))]
    revert h
    simp only [antipode]
    cases u i <;> cases z i <;> simp
end AaronsonAmbainis.DetBij
