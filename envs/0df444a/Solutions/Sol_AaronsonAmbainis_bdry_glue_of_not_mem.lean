-- Prove2me | solution 1 for AaronsonAmbainis.bdry_glue_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:04.812106+00:00
-- url     : https://prove2.me/submissions/a9a426e1-3eb1-423a-98e4-d0b44d6682bb

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_glue_flipSet_singleton_of_not_mem


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∉ F)
    (z : Cube ι) : bdry (fun u => g (glue F z u)) j = 0 := by
  unfold bdry
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  simp only [glue_flipSet_singleton_of_not_mem hj]
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact Bool.noConfusion h2
end AaronsonAmbainis
