-- Prove2me | solution 1 for AaronsonAmbainis.allPairs_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:40.229835+00:00
-- url     : https://prove2.me/submissions/5cd4a089-5d90-4dc5-9e8f-686df0deb448

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_isRow_glue
import Theorems.Thm_AaronsonAmbainis_zone_sum_glue
import Theorems.Thm_AaronsonAmbainis_bdry_glue_of_not_mem
import Theorems.Thm_AaronsonAmbainis_sum_bdry_glue_of_mem
import Theorems.Thm_AaronsonAmbainis_sum_sum_glue


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (hAntipodal : AntipodalInequality) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (lam : Cube ι → ι → ℝ) (hlam : ∀ x, IsRow g x (lam x)) (F : Finset ι) :
    ∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, (bdry g j : ℝ) / w j := by
  -- the antipodal inequality on the subcube through `z`
  have hz : ∀ z : Cube ι, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j := by
    intro z
    have h := hAntipodal ι (fun u => g (glue F z u)) w hw
      (fun u j => if j ∈ F then lam (glue F z u) j else 0) (fun u => isRow_glue hlam F z u)
    rw [← zone_sum_glue]
    exact h
  -- add over all `z`
  have hsum : ∑ z, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j :=
    Finset.sum_le_sum fun z _ => hz z
  rw [sum_sum_glue] at hsum
  have hj : ∀ j, ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = if j ∈ F then 2 ^ Fintype.card ι * ((bdry g j : ℝ) / w j) else 0 := by
    intro j
    split_ifs with hjF
    · rw [← Finset.sum_div, sum_bdry_glue_of_mem g hjF, mul_div_assoc]
    · apply Finset.sum_eq_zero
      intro z _
      rw [bdry_glue_of_not_mem g hjF z]
      simp
  have hR : ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = 2 ^ Fintype.card ι * ∑ j ∈ F, (bdry g j : ℝ) / w j := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hj j), Fintype.sum_ite_mem,
      Finset.mul_sum]
  rw [hR] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity)
end AaronsonAmbainis
