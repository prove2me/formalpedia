-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityInnovation_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:06:40.562199+00:00
-- url     : https://prove2.me/submissions/3439cecf-84b2-4103-981a-06cccc75d582

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  (∑ ω : Ω, w ω * (finiteMortalityInnovation w K t ω) ^ 2) =
    finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by
  let q := finiteMortalityDeathRate w K t
  have hpoint (ω : Ω) :
      w ω * (finiteMortalityInnovation w K t ω) ^ 2 =
        (if K ω = t then w ω else 0) * (1 - 2 * q) +
          (if t ≤ K ω then w ω else 0) * q ^ 2 := by
    by_cases hd : K ω = t
    · have hs : t ≤ K ω := by omega
      simp [finiteMortalityInnovation, hd, hs, q]
      ring
    · by_cases hs : t ≤ K ω
      · simp [finiteMortalityInnovation, hd, hs, q]
      · simp [finiteMortalityInnovation, hd, hs, q]
  have hm :
      (∑ ω : Ω, w ω * (finiteMortalityInnovation w K t ω) ^ 2) =
        finiteMortalityDeathMass w K t * (1 - 2 * q) +
          finiteMortalitySurvivalMass w K t * q ^ 2 := by
    calc
      (∑ ω : Ω, w ω * (finiteMortalityInnovation w K t ω) ^ 2) =
        ∑ ω : Ω, ((if K ω = t then w ω else 0) * (1 - 2 * q) +
          (if t ≤ K ω then w ω else 0) * q ^ 2) := by
            apply Finset.sum_congr rfl
            intro ω _
            exact hpoint ω
      _ = (∑ ω : Ω, if K ω = t then w ω else 0) * (1 - 2 * q) +
            (∑ ω : Ω, if t ≤ K ω then w ω else 0) * q ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = finiteMortalityDeathMass w K t * (1 - 2 * q) +
            finiteMortalitySurvivalMass w K t * q ^ 2 := by
              rfl
  have hp : finiteMortalitySurvivalMass w K t =
      finiteMortalityDeathMass w K t + finiteMortalitySurvivalMass w K (t + 1) := by
    unfold finiteMortalitySurvivalMass finiteMortalityDeathMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : K ω = t
    · have ht : t ≤ K ω := by omega
      have ht1 : ¬ t + 1 ≤ K ω := by omega
      simp [h, ht, ht1]
    · by_cases ht : t ≤ K ω
      · have ht1 : t + 1 ≤ K ω := by omega
        simp [h, ht, ht1]
      · have ht1 : ¬ t + 1 ≤ K ω := by omega
        simp [h, ht, ht1]
  rw [hm]
  simp only [q, finiteMortalityDeathRate, finiteMortalitySurvivalRate]
  have hs : finiteMortalitySurvivalMass w K t ≠ 0 := ne_of_gt hS
  field_simp
  rw [hp]
  ring
