-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityInnovation_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:03:24.386768+00:00
-- url     : https://prove2.me/submissions/96342403-7059-443a-aec3-9f05e2e69cba

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_expected_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (i j : ℕ) (hij : i < j) (hSj : 0 < finiteMortalitySurvivalMass w K j)
  :
  (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω * finiteMortalityInnovation w K j ω) = 0 := by
  have hz : (∑ ω : Ω, w ω * finiteMortalityInnovation w K j ω) = 0 :=
    finiteMortalityInnovation_expected_zero w K j hSj
  have hp (ω : Ω) :
      finiteMortalityInnovation w K i ω * finiteMortalityInnovation w K j ω =
        -(finiteMortalityDeathRate w K i) * finiteMortalityInnovation w K j ω := by
    by_cases hj : K ω < j
    · have hnj : K ω ≠ j := by omega
      have hnot : ¬ j ≤ K ω := by omega
      simp [finiteMortalityInnovation, hnj, hnot]
    · have hni : K ω ≠ i := by omega
      have hle : i ≤ K ω := by omega
      simp [finiteMortalityInnovation, hni, hle]
  calc
    (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω *
        finiteMortalityInnovation w K j ω) =
      -(finiteMortalityDeathRate w K i) *
        (∑ ω : Ω, w ω * finiteMortalityInnovation w K j ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          calc
            w ω * finiteMortalityInnovation w K i ω *
                finiteMortalityInnovation w K j ω =
              w ω * (finiteMortalityInnovation w K i ω *
                finiteMortalityInnovation w K j ω) := by ring
            _ = w ω * (-(finiteMortalityDeathRate w K i) *
                finiteMortalityInnovation w K j ω) := by rw [hp ω]
            _ = -(finiteMortalityDeathRate w K i) *
                (w ω * finiteMortalityInnovation w K j ω) := by ring
    _ = 0 := by rw [hz]; ring
