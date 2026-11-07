-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:13.870659+00:00
-- url     : https://prove2.me/submissions/5359f7d9-a12b-466a-8c80-601c90b362b7

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]
end AaronsonAmbainis.Bridge
