-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.mem_Up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:21:15.885506+00:00
-- url     : https://prove2.me/submissions/e2a34000-76ee-4866-914e-3a2d6d5052b7

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Up g j ↔ x.1 j = true ∧ g (flipSet x.1 {j}) = true := by
  simp [Up]
end AaronsonAmbainis.DetLow
