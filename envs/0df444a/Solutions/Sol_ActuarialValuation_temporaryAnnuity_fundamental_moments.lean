-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuity_fundamental_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:39:18.401364+00:00
-- url     : https://prove2.me/submissions/a5c450dc-21ed-4f3d-b3aa-248fb0226b2d

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_expectation
import Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_expectation
import Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_secondMoment
import Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_secondMoment
import Theorems.Thm_ActuarialValuation_temporaryAnnuityDue_variance
import Theorems.Thm_ActuarialValuation_temporaryAnnuityImmediate_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    ((∫ ω, temporaryAnnuityDuePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal)
    ∧ ((∫ ω, temporaryAnnuityImmediatePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal)
    ∧ ((∫ ω, (temporaryAnnuityDuePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal)
    ∧ ((∫ ω, (temporaryAnnuityImmediatePV K v n ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal)
    ∧ (ProbabilityTheory.variance (temporaryAnnuityDuePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ i) * (v ^ j) * (P (curtateSurvivalEvent K (max i j))).toReal) - (∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal) ^ 2)
    ∧ (ProbabilityTheory.variance (temporaryAnnuityImmediatePV K v n) P = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v ^ (i + 1)) * (v ^ (j + 1)) * (P (curtateSurvivalEvent K (max (i + 1) (j + 1)))).toReal) - (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal) ^ 2) := by
  exact ⟨
    temporaryAnnuityDue_expectation P K hK v n,
    temporaryAnnuityImmediate_expectation P K hK v n,
    temporaryAnnuityDue_secondMoment P K hK v n,
    temporaryAnnuityImmediate_secondMoment P K hK v n,
    temporaryAnnuityDue_variance P K hK v n,
    temporaryAnnuityImmediate_variance P K hK v n⟩
