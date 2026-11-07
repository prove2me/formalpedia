-- Prove2me | solution 1 for AaronsonAmbainis.Row.natDegree_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:24.694509+00:00
-- url     : https://prove2.me/submissions/8d052b70-87d2-4674-b258-001a1551b9da

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Row
theorem _root_.solution (g : Finset β → ℝ) (R : Finset β) (D : ℕ)
    (hg : ∀ U : Finset β, D < U.card → g U = 0) : (phi g R).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ (fun U _ => ?_)
  by_cases hU : U.card ≤ D
  · have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    calc (C (g U) * (1 - X) ^ (U ∩ R).card).natDegree
        ≤ ((1 - X : ℝ[X]) ^ (U ∩ R).card).natDegree := natDegree_C_mul_le _ _
      _ ≤ (U ∩ R).card * (1 - X : ℝ[X]).natDegree := natDegree_pow_le
      _ ≤ (U ∩ R).card * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by
          rw [mul_one]
          exact (Finset.card_le_card Finset.inter_subset_left).trans hU
  · rw [hg U (not_le.mp hU)]
    simp
end AaronsonAmbainis.Row
