-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:11.929365+00:00
-- url     : https://prove2.me/submissions/83180823-ce98-48ad-9b14-6ac613f7d89d

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]
end AaronsonAmbainis.Bridge
