-- Prove2me | solution 1 for AaronsonAmbainis.glue_antipode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:51.200988+00:00
-- url     : https://prove2.me/submissions/52b3c042-3aea-44ba-a016-b79240e35b1d

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (F : Finset ι) (z u : Cube ι) :
    glue F z (antipode u) = flipSet (glue F z u) F := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, flipSet, antipode, hF]
end AaronsonAmbainis
