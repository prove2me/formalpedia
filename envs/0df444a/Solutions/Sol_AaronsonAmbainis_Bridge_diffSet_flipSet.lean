-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.diffSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:54.311197+00:00
-- url     : https://prove2.me/submissions/4ed7447d-e41b-46d4-9a82-5f2264cefd49

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]
end AaronsonAmbainis.Bridge
