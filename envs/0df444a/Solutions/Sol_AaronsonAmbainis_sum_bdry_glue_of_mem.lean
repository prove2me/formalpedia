-- Prove2me | solution 1 for AaronsonAmbainis.sum_bdry_glue_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:09.162445+00:00
-- url     : https://prove2.me/submissions/3e272864-8a63-4b7a-9411-b76b1fd0f947

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_bdry_eq_sum
import Theorems.Thm_AaronsonAmbainis_glue_flipSet_singleton_of_mem
import Theorems.Thm_AaronsonAmbainis_sum_sum_glue


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∈ F) :
    ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) = 2 ^ Fintype.card ι * (bdry g j : ℝ) := by
  have h1 : ∀ z, (bdry (fun u => g (glue F z u)) j : ℝ)
      = ∑ u, (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)
          (glue F z u) := by
    intro z
    rw [bdry_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [glue_flipSet_singleton_of_mem hj]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), bdry_eq_sum]
  exact sum_sum_glue F (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)
end AaronsonAmbainis
