-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_singleton_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:11:14.095512+00:00
-- url     : https://prove2.me/submissions/d42a0a48-dbf8-44cb-b23d-e1e1d5a42009

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) {i j : ι} (h : i ≠ j) : flipSet x {j} i = x i := by
  simp [flipSet, h]
end AaronsonAmbainis.Bridge
