-- Prove2me | solution 1 for ActuarialValuation.premiumDuePV_expectation_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:05:08.153329+00:00
-- url     : https://prove2.me/submissions/413745b2-d60e-4f56-8f08-66be3e8a216c

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Theorems.Thm_ActuarialValuation_premiumDuePV_first_payment
import Theorems.Thm_ActuarialValuation_premiumDuePV_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ) (hn : 0 < n) (hv : 0 ≤ v)
    : 0 < ∫ ω, premiumDuePV K v n ω ∂P := by
  have hInt : Integrable (premiumDuePV K v n) P :=
    premiumDuePV_integrable P K hK v n
  have hle : (∫ ω : Ω, (1 : ℝ) ∂P) ≤
      ∫ ω, premiumDuePV K v n ω ∂P := by
    apply integral_mono (integrable_const (1 : ℝ)) hInt
    intro ω
    exact premiumDuePV_first_payment K v n ω hn hv
  have hone : (∫ ω : Ω, (1 : ℝ) ∂P) = 1 := by simp
  linarith
