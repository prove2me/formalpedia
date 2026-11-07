-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.mem_Dn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:54:19.184636+00:00
-- url     : https://prove2.me/submissions/350b40d0-2161-4e25-a438-2b40c5f20e3c

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
    x ∈ Dn g j ↔ x.1 j = false ∧ g (flipSet x.1 {j}) = true := by
  simp [Dn]
end AaronsonAmbainis.DetLow
