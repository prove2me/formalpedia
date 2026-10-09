-- Prove2me | solution 1 for ActuarialValuation.wholeLife_deferredAnnuity_fundamental_valuation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:21:19.159013+00:00
-- url     : https://prove2.me/submissions/b9c7fe50-5e45-4c23-8ea9-dd05ca9f13bb

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV
import Definitions.Def_actuarial_deferredAnnuityDuePV
import Definitions.Def_actuarial_deferredAnnuityImmediatePV
import Theorems.Thm_ActuarialValuation_wholeLifeDue_expectation
import Theorems.Thm_ActuarialValuation_wholeLifeImmediate_expectation
import Theorems.Thm_ActuarialValuation_deferredDue_expectation
import Theorems.Thm_ActuarialValuation_deferredImmediate_expectation
import Theorems.Thm_ActuarialValuation_deferredDue_eq_whole_minus_temporary
import Theorems.Thm_ActuarialValuation_deferredImmediate_eq_whole_minus_temporary
import Theorems.Thm_ActuarialValuation_wholeLifeImmediate_eq_due_sub_one
import Theorems.Thm_ActuarialValuation_deferredDue_expectation_eq_whole_sub_temporary
import Theorems.Thm_ActuarialValuation_deferredImmediate_expectation_eq_whole_sub_temporary

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
    ((∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) = ∑' k : ℕ, v ^ k * (P (curtateSurvivalEvent K k)).toReal)
    ∧ ((∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) = ∑' k : ℕ, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)
    ∧ ((∫ ω, deferredAnnuityDuePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ k * (P (curtateSurvivalEvent K k)).toReal else 0)
    ∧ ((∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = ∑' k : ℕ, if n ≤ k then v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal else 0)
    ∧ (∀ ω, deferredAnnuityDuePV K v n ω = wholeLifeAnnuityDuePV K v ω - (∑ k ∈ Finset.range n, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω))
    ∧ (∀ ω, deferredAnnuityImmediatePV K v n ω = wholeLifeAnnuityImmediatePV K v ω - (∑ k ∈ Finset.range n, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω))
    ∧ (∀ ω, wholeLifeAnnuityImmediatePV K v ω = wholeLifeAnnuityDuePV K v ω - 1)
    ∧ ((∫ ω, deferredAnnuityDuePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityDuePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal))
    ∧ ((∫ ω, deferredAnnuityImmediatePV K v n ω ∂P) = (∫ ω, wholeLifeAnnuityImmediatePV K v ω ∂P) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)) := by
  constructor
  · exact wholeLifeDue_expectation P K hK v hv0 hv1
  constructor
  · exact wholeLifeImmediate_expectation P K hK v hv0 hv1
  constructor
  · exact deferredDue_expectation P K hK v hv0 hv1 n
  constructor
  · exact deferredImmediate_expectation P K hK v hv0 hv1 n
  constructor
  · intro ω
    exact deferredDue_eq_whole_minus_temporary K v n ω
  constructor
  · intro ω
    exact deferredImmediate_eq_whole_minus_temporary K v n ω
  constructor
  · intro ω
    exact wholeLifeImmediate_eq_due_sub_one K v ω
  constructor
  · exact deferredDue_expectation_eq_whole_sub_temporary P K hK v hv0 hv1 n
  · exact deferredImmediate_expectation_eq_whole_sub_temporary P K hK v hv0 hv1 n
