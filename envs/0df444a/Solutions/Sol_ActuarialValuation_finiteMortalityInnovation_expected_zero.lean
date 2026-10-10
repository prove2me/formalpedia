-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityInnovation_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:55:04.142934+00:00
-- url     : https://prove2.me/submissions/93f14a7b-b638-4816-953b-7d281b02f06f

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω) = 0 := by
  calc
    (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω) =
      (∑ ω : Ω, if K ω = t then w ω else 0) -
        finiteMortalityDeathRate w K t * (∑ ω : Ω, if t ≤ K ω then w ω else 0) := by
          simp_rw [finiteMortalityInnovation, mul_sub]
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl
            intro ω _
            split_ifs <;> ring
          · apply Finset.sum_congr rfl
            intro ω _
            split_ifs <;> ring
    _ = 0 := by
      change finiteMortalityDeathMass w K t -
        (finiteMortalityDeathMass w K t / finiteMortalitySurvivalMass w K t) *
        finiteMortalitySurvivalMass w K t = 0
      rw [div_mul_cancel₀ _ (ne_of_gt hS)]
      ring
