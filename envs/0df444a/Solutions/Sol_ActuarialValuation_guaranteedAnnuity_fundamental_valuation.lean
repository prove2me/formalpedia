-- Prove2me | solution 1 for ActuarialValuation.guaranteedAnnuity_fundamental_valuation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:54:22.494622+00:00
-- url     : https://prove2.me/submissions/0580587f-fdbf-46c8-af22-ccc622ca632f

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
import Definitions.Def_actuarial_annuityCertainDuePV
import Definitions.Def_actuarial_annuityCertainImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Theorems.Thm_ActuarialValuation_guaranteedDue_eq_certain_add_deferred
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_eq_certain_add_deferred
import Theorems.Thm_ActuarialValuation_guaranteedDue_expectation_survival_tsum
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_expectation_survival_tsum
import Theorems.Thm_ActuarialValuation_guaranteedDue_variance_eq_deferred
import Theorems.Thm_ActuarialValuation_guaranteedImmediate_variance_eq_deferred
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ)
    :
    (∀ ω, guaranteedAnnuityDuePV K v n ω =
      annuityCertainDuePV v n + deferredAnnuityDuePV K v n ω)
    ∧ (∀ ω, guaranteedAnnuityImmediatePV K v n ω =
      annuityCertainImmediatePV v n + deferredAnnuityImmediatePV K v n ω)
    ∧ ((∫ ω, guaranteedAnnuityDuePV K v n ω ∂P) =
      annuityCertainDuePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0)
    ∧ ((∫ ω, guaranteedAnnuityImmediatePV K v n ω ∂P) =
      annuityCertainImmediatePV v n +
      ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0)
    ∧ (ProbabilityTheory.variance (guaranteedAnnuityDuePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityDuePV K v n) P)
    ∧ (ProbabilityTheory.variance (guaranteedAnnuityImmediatePV K v n) P =
      ProbabilityTheory.variance (deferredAnnuityImmediatePV K v n) P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact guaranteedDue_eq_certain_add_deferred K v n ω
  · intro ω
    exact guaranteedImmediate_eq_certain_add_deferred K v n ω
  · exact guaranteedDue_expectation_survival_tsum P K hK v hv0 hv1 n
  · exact guaranteedImmediate_expectation_survival_tsum P K hK v hv0 hv1 n
  · exact guaranteedDue_variance_eq_deferred P K hK v hv0 hv1 n
  · exact guaranteedImmediate_variance_eq_deferred P K hK v hv0 hv1 n
