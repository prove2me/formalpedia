-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:43.24038+00:00
-- url     : https://prove2.me/submissions/cb0ea4dd-42cf-46c9-8605-2321bea38572

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_self

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Bridge
theorem _root_.solution [DecidableEq ι] (j : ι) (x : Cube ι) : dict j (flipSet x {j}) = -dict j x := by
  unfold dict
  rw [flipSet_singleton_self]
  cases x j <;> simp
end AaronsonAmbainis.Bridge
