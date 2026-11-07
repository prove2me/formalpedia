-- Prove2me | solution 1 for AaronsonAmbainis.mem_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:58.915035+00:00
-- url     : https://prove2.me/submissions/2d75edbd-1033-41d8-8d0a-526982d1ef8f

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {x y : Cube ι} {i : ι} : i ∈ diffSet x y ↔ x i ≠ y i := by
  simp [diffSet]
end AaronsonAmbainis
