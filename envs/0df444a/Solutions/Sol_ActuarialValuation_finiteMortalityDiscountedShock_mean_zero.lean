-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityDiscountedShock_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:03:28.841989+00:00
-- url     : https://prove2.me/submissions/ed422d9b-f6e7-41cf-ac8a-611b28702d5a

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_expected_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (n : ℕ)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K ρ n ω) = 0 := by
  have hz (t : ℕ) (ht : t ∈ Finset.range n) :
      (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω) = 0 :=
    finiteMortalityInnovation_expected_zero w K t (hS t ht)
  calc
    (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K ρ n ω) =
      ∑ t ∈ Finset.range n, ρ t *
        (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω) := by
          simp_rw [finiteMortalityDiscountedShock, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [hz t ht]
      ring
