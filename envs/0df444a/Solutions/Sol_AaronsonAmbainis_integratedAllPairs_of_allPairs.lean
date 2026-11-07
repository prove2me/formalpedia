-- Prove2me | solution 1 for AaronsonAmbainis.integratedAllPairs_of_allPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:44.021207+00:00
-- url     : https://prove2.me/submissions/0e368aee-1b9c-4a97-81d1-8ebde4e781e2

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
import Theorems.Thm_AaronsonAmbainis_Level_integrated_four_mul
import Theorems.Thm_AaronsonAmbainis_Level_four_pow_card


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : AllPairsInequality → IntegratedAllPairsInequality := by
  intro hAllPairs ι _ _ f a ha hrow w hw
  have h := Level.integrated_four_mul hAllPairs f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y hy
      have hlt := (Finset.mem_filter.mp hy).2
      rw [Subsingleton.elim y x] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [hL, Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero]
  · rw [Level.four_pow_card, mul_assoc] at h
    linarith
end AaronsonAmbainis
