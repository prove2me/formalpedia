-- Prove2me | solution 1 for ActuarialValuation.fundamental_contingent_valuation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:18:27.253967+00:00
-- url     : https://prove2.me/submissions/6f12cacf-b371-46cd-882f-a18d1a564ebc

import Mathlib
import Definitions.Def_actuarial_presentValue
import Theorems.Thm_ActuarialValuation_presentValue_expectation
import Theorems.Thm_ActuarialValuation_presentValue_secondMoment
import Theorems.Thm_ActuarialValuation_presentValue_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

/-- Proof template from a successful private Prove2Me compiler preflight.
Publication-time imports and the 'theorem solution' wrapper are not yet verified. -/
theorem solution {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω)
    (htrigger : ∀ i ∈ payments, MeasurableSet (trigger i)) :
    (∫ ω, presentValue payments time discount amount trigger ω ∂P =
      ∑ i ∈ payments, discount (time i) * amount i *
        (P (trigger i)).toReal) ∧
    (∫ ω, (presentValue payments time discount amount trigger ω) ^ 2 ∂P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          (P (trigger i ∩ trigger j)).toReal) ∧
    (ProbabilityTheory.variance
      (presentValue payments time discount amount trigger) P =
      ∑ i ∈ payments, ∑ j ∈ payments,
        (discount (time i) * amount i) *
          (discount (time j) * amount j) *
          ((P (trigger i ∩ trigger j)).toReal -
            (P (trigger i)).toReal * (P (trigger j)).toReal)) := by
  exact ⟨
    presentValue_expectation P payments time discount amount trigger htrigger,
    presentValue_secondMoment P payments time discount amount trigger htrigger,
    presentValue_variance P payments time discount amount trigger htrigger
  ⟩
