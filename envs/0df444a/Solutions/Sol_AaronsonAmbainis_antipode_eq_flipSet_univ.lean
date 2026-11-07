-- Prove2me | solution 1 for AaronsonAmbainis.antipode_eq_flipSet_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:45.716983+00:00
-- url     : https://prove2.me/submissions/a9bbd89f-1665-424a-bdf3-68c77c495fb1

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [flipSet, antipode]
end AaronsonAmbainis
