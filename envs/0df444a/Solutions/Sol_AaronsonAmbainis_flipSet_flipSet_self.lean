-- Prove2me | solution 1 for AaronsonAmbainis.flipSet_flipSet_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:18.24721+00:00
-- url     : https://prove2.me/submissions/f44713c6-850c-4514-bcca-1b382969318b

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]
end AaronsonAmbainis
