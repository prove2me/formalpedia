-- Prove2me | solution 1 for AaronsonAmbainis.isRow_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:23.454206+00:00
-- url     : https://prove2.me/submissions/b8d7d43f-60ef-4927-9bde-6172f3136716

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_glue_flipSet


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} (hlam : ∀ x, IsRow g x (lam x))
    (F : Finset ι) (z u : Cube ι) :
    IsRow (fun u => g (glue F z u)) u (fun j => if j ∈ F then lam (glue F z u) j else 0) := by
  constructor
  · intro j
    dsimp only
    split_ifs
    · exact (hlam _).1 j
    · exact le_rfl
  · intro S hS
    have hS' : g (flipSet (glue F z u) (S ∩ F)) ≠ g (glue F z u) := by
      rw [← glue_flipSet]
      exact hS
    calc (1 : ℝ) ≤ ∑ j ∈ S ∩ F, lam (glue F z u) j := (hlam (glue F z u)).2 (S ∩ F) hS'
      _ = ∑ j ∈ S, if j ∈ F then lam (glue F z u) j else 0 :=
          (Finset.sum_ite_mem S F (fun j => lam (glue F z u) j)).symm
end AaronsonAmbainis
