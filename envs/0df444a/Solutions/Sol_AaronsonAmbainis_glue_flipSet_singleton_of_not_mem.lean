-- Prove2me | solution 1 for AaronsonAmbainis.glue_flipSet_singleton_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:20.028319+00:00
-- url     : https://prove2.me/submissions/35153981-df62-49bc-b478-e0aa5ac12710

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Theorems.Thm_AaronsonAmbainis_glue_flipSet
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {F : Finset ι} {j : ι} (hj : j ∉ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = glue F z u := by
  rw [glue_flipSet, Finset.singleton_inter_of_notMem hj, flipSet_empty]
end AaronsonAmbainis
