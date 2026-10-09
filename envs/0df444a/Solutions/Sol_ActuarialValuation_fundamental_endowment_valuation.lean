-- Prove2me | solution 1 for ActuarialValuation.fundamental_endowment_valuation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:46:49.521995+00:00
-- url     : https://prove2.me/submissions/254643f7-1c71-4bf1-9c0e-c3b696edddbe

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_pureEndowmentPV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_deathYearEvent
import Theorems.Thm_ActuarialValuation_exact_curtate_survival_gap
import Theorems.Thm_ActuarialValuation_pureEndowment_expectation
import Theorems.Thm_ActuarialValuation_pureEndowment_variance
import Theorems.Thm_ActuarialValuation_endowmentPV_decomposition
import Theorems.Thm_ActuarialValuation_endowment_expectation
import Theorems.Thm_ActuarialValuation_endowment_secondMoment
import Theorems.Thm_ActuarialValuation_endowment_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (K : Ω → ℕ) (hK : Measurable K)
    (hKT : ∀ ω, (K ω : ℝ) ≤ T ω ∧ T ω < (K ω : ℝ) + 1) (v : ℝ) (n : ℕ)
    : ((strictSurvivalEvent T n) ∪ {ω | T ω = (n : ℝ)} = (curtateSurvivalEvent K n))
    ∧ ((∫ ω, pureEndowmentPV T v n ω ∂P) = v ^ n * (P (strictSurvivalEvent T n)).toReal)
    ∧ (ProbabilityTheory.variance (pureEndowmentPV T v n) P = (v ^ n) ^ 2 * (P (strictSurvivalEvent T n)).toReal * (1 - (P (strictSurvivalEvent T n)).toReal))
    ∧ (∀ ω, endowmentAssurancePV K v n ω = termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω)
    ∧ ((∫ ω, endowmentAssurancePV K v n ω ∂P) = (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal)
    ∧ ((∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) = (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal)
    ∧ (ProbabilityTheory.variance (endowmentAssurancePV K v n) P = ((∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal) - ((∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal) ^ 2) := by
  have hTnonneg : ∀ ω, 0 ≤ T ω := by
    intro ω
    have hKnonneg : (0 : ℝ) ≤ (K ω : ℝ) := Nat.cast_nonneg (K ω)
    exact le_trans hKnonneg (hKT ω).1
  refine ⟨exact_curtate_survival_gap T K n hKT,
    pureEndowment_expectation P T hT hTnonneg v n,
    pureEndowment_variance P T hT hTnonneg v n,
    ?_, endowment_expectation P K hK v n,
    endowment_secondMoment P K hK v n,
    endowment_variance P K hK v n⟩
  intro ω
  exact endowmentPV_decomposition K v n ω
