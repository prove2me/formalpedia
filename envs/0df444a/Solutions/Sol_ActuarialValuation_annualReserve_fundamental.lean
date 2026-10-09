-- Prove2me | solution 1 for ActuarialValuation.annualReserve_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T08:34:27.576908+00:00
-- url     : https://prove2.me/submissions/6d14cda8-f845-42b5-9059-328a19fc8f88

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualProspectiveReserve
import Definitions.Def_actuarial_annualSurvivalMass
import Theorems.Thm_ActuarialValuation_annualDeathSurvival_probabilities_sum
import Theorems.Thm_ActuarialValuation_annualReserve_one_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
  (hK : Measurable K) (v : ℝ) (n t : ℕ) (b π : ℝ)
  (ht : t < n) (hS : 0 < annualSurvivalMass P K t)
  (hNext : 0 < annualSurvivalMass P K (t + 1)) :
  (annualDeathMass P K t / annualSurvivalMass P K t +
    annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t = 1)
  ∧ (annualProspectiveReserve P K v n t b π + π =
    v * (annualDeathMass P K t / annualSurvivalMass P K t * b +
      annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t *
        annualProspectiveReserve P K v n (t + 1) b π)) := by
  exact ⟨
    annualDeathSurvival_probabilities_sum P K hK t hS,
    annualReserve_one_step P K hK v n t b π ht hS hNext⟩
