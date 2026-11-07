-- Prove2me | solution 1 for AaronsonAmbainis.card_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:38.014642+00:00
-- url     : https://prove2.me/submissions/be5a311a-2f61-48e7-9950-d0bdd7d3fb74

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
  simp [Cube]
end AaronsonAmbainis
