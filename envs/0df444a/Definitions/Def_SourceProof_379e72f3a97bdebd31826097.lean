-- Prove2me | Definitions.Def_SourceProof_379e72f3a97bdebd31826097
-- name    : SourceProof_379e72f3a97bdebd31826097
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:07:52.091163+00:00
-- url     : https://prove2.me/theorems/1f2104fc-bd37-495b-b394-b2731f05b2bd
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum_exists
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

end CappedShift

section Reindex


theorem _root_.Prove2MeSourceProof.h_379e72f3a97bdebd31826097 {K m : ℕ} {θ : Fin K → ℝ} {σ : ℕ → WithTop ℝ}
    {T : ℝ} (hθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, σ i = ((v : ℝ) : WithTop ℝ) ∧ 0 < v ∧ v ≤ T})
    (hσmono : Monotone σ) (hσ0 : σ 0 = ((0 : ℝ) : WithTop ℝ))
    (hstrict : ∀ i : ℕ, σ (i + 1) ≤ ((T : ℝ) : WithTop ℝ) → σ i < σ (i + 1))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m) (G' : ℕ → ℝ) (G : Fin K → ℝ)
    (hex : ∀ k : ℕ, σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, σ (k + 1) = ((θ j : ℝ) : WithTop ℝ) ∧ G' k = G j) :
    (∑ k ∈ Finset.range m,
        if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G' k else 0)
      = ∑ j : Fin K, G j := by
  classical
  rcases isEmpty_or_nonempty (Fin K) with hK | hK
  · have hzero : ∀ k : ℕ,
        (if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G' k else 0) = 0 := by
      intro k
      by_cases hp : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ)
      · exact absurd (hex k hp) fun h => hK.false h.choose
      · exact if_neg hp
    rw [Finset.sum_congr rfl fun k _ => hzero k, Finset.sum_const_zero,
      Finset.sum_eq_zero fun j _ => (hK.false j).elim]
  · obtain ⟨j₀⟩ := hK
    refine (Finset.sum_congr rfl fun k _ => ?_).trans
      (LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum hθ hmemθ hrange hσmono hσ0 hstrict hm
        (fun k => if h : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then (hex k h).choose else j₀)
        (fun k h => by rw [dif_pos h]; exact (hex k h).choose_spec.1) G)
    by_cases hp : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp, if_pos hp, dif_pos hp]
      exact (hex k hp).choose_spec.2
    · rw [if_neg hp, if_neg hp]
end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end MarkIdentification

end LevyStochCalc.Ito.JumpFormula


