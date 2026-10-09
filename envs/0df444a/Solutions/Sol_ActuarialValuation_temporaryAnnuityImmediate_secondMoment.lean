-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityImmediate_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:30:56.576011+00:00
-- url     : https://prove2.me/submissions/550ffe18-039f-4cff-9ed4-6fcb85ce822d

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, (temporaryAnnuityImmediatePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K (k + 1)) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici (k + 1))
    exact hK measurableSet_Ici
  have hinter : ∀ (a b : ℕ),
      curtateSurvivalEvent K a ∩ curtateSurvivalEvent K b =
      curtateSurvivalEvent K (max a b) := by
    intro a b
    ext ω
    change (a ≤ K ω ∧ b ≤ K ω) ↔ max a b ≤ K ω
    exact max_le_iff.symm
  unfold temporaryAnnuityImmediatePV
  simpa only [mul_one, hinter] using
    (presentValue_secondMoment P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ))
      (fun k : ℕ => curtateSurvivalEvent K (k + 1)) htrigger)
