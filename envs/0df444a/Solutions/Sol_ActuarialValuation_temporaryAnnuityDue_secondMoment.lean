-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityDue_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:30:52.796509+00:00
-- url     : https://prove2.me/submissions/0b7739dc-e430-43f9-9190-eec8c6d6d45e

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
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
    (∫ ω, (temporaryAnnuityDuePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici k)
    exact hK measurableSet_Ici
  have hinter : ∀ (a b : ℕ),
      curtateSurvivalEvent K a ∩ curtateSurvivalEvent K b =
      curtateSurvivalEvent K (max a b) := by
    intro a b
    ext ω
    change (a ≤ K ω ∧ b ≤ K ω) ↔ max a b ≤ K ω
    exact max_le_iff.symm
  unfold temporaryAnnuityDuePV
  simpa only [mul_one, hinter] using
    (presentValue_secondMoment P (Finset.range n)
      (fun k : ℕ => k) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (curtateSurvivalEvent K) htrigger)
