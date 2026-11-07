-- Prove2me | solution 1 for AaronsonAmbainis.glue_flipSet_singleton_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:17.065714+00:00
-- url     : https://prove2.me/submissions/1d1769a2-85f4-424b-ab28-24964c97cbb6

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Theorems.Thm_AaronsonAmbainis_glue_flipSet

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {F : Finset ι} {j : ι} (hj : j ∈ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = flipSet (glue F z u) {j} := by
  rw [glue_flipSet, Finset.singleton_inter_of_mem hj]
end AaronsonAmbainis
