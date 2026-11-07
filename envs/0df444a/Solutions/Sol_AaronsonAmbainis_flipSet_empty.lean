-- Prove2me | solution 1 for AaronsonAmbainis.flipSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:26.796124+00:00
-- url     : https://prove2.me/submissions/218b6de3-3a3e-48d4-8fa2-07977c3cc34b

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]
end AaronsonAmbainis
