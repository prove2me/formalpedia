-- Prove2me | solution 1 for AaronsonAmbainis.allPairs_of_antipodal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:52.652248+00:00
-- url     : https://prove2.me/submissions/86315d2e-e810-4a3d-9346-2ecda3a4c12e

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
import Theorems.Thm_AaronsonAmbainis_sum_allPairsTerm
import Theorems.Thm_AaronsonAmbainis_two_mul_sum_finset_sum
import Theorems.Thm_AaronsonAmbainis_allPairs_core


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution : AntipodalInequality → AllPairsInequality := by
  intro hAntipodal ι _ _ g w hw lam hlam
  -- the left side as a sum of the terms of all the inequalities `allPairs_core`
  have hL : ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      = ∑ x, ∑ F : Finset ι, allPairsTerm g w lam F x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : g x = true
    · rw [if_pos hx, sum_allPairsTerm, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = false
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]
      · rw [if_neg hy, if_neg (fun h => hy h.2)]
    · rw [if_neg hx, sum_allPairsTerm]
      symm
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => hx h.1)]
  -- `allPairs_core` for every `F`, added up
  have hF : ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j :=
    Finset.sum_le_sum fun F _ => allPairs_core hAntipodal g w hw lam hlam F
  rw [hL, Finset.sum_comm]
  calc 2 * ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ 2 * ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j := by linarith
    _ = 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j :=
        two_mul_sum_finset_sum (fun j => (bdry g j : ℝ) / w j)
end AaronsonAmbainis
