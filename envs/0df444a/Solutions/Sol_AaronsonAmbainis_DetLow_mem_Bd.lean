-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.mem_Bd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:54:24.555044+00:00
-- url     : https://prove2.me/submissions/ddeb29c2-76ca-492e-be03-4b78f2b1d91f

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Bd g j ↔ g (flipSet x.1 {j}) = false := by
  simp [Bd]
end AaronsonAmbainis.DetLow
