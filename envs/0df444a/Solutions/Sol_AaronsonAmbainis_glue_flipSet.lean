-- Prove2me | solution 1 for AaronsonAmbainis.glue_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:43.176234+00:00
-- url     : https://prove2.me/submissions/7309d793-2e38-4f2a-b1f9-92267559266b

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (F : Finset ι) (z u : Cube ι) (S : Finset ι) :
    glue F z (flipSet u S) = flipSet (glue F z u) (S ∩ F) := by
  funext i
  by_cases hF : i ∈ F <;> by_cases hS : i ∈ S <;> simp [glue, flipSet, hF, hS]
end AaronsonAmbainis
