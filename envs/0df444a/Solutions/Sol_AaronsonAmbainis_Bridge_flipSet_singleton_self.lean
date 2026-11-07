-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_singleton_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:15.425244+00:00
-- url     : https://prove2.me/submissions/5a28d3a5-0380-4f37-9680-9513a6ca81d6

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) (j : ι) : flipSet x {j} j = !(x j) := by
  simp [flipSet]
end AaronsonAmbainis.Bridge
