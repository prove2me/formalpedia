-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:02:12.178188+00:00
-- url     : https://prove2.me/theorems/bd53fd4b-7d68-4205-b4c6-633be592f390
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000

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

end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Enlarging the first factor's `σ`-algebra enlarges the product `σ`-algebra. -/
theorem prod_le_prod_left {α : Type*} [MeasurableSpace α]
    {m₁ m₂ : MeasurableSpace Ω} (h : m₁ ≤ m₂) :
    @Prod.instMeasurableSpace Ω α m₁ inferInstance
      ≤ @Prod.instMeasurableSpace Ω α m₂ inferInstance :=
  sup_le_sup_right (MeasurableSpace.comap_mono h) _
omit [MeasurableSpace E] in
/-- A process progressively measurable for a filtration is progressively measurable for any
larger filtration. -/
theorem progressivelyMeasurable_of_le {H : Ω → ℝ → ℝ}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (hle : ℱ ≤ 𝒢)
    (h : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable 𝒢 H :=
  fun t => (h t).mono (prod_le_prod_left (hle t))
/-- A marked process progressively measurable for a filtration is progressively measurable for
any larger filtration. -/
theorem markedProgressivelyMeasurable_of_le {φ : Ω → ℝ → E → ℝ}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (hle : ℱ ≤ 𝒢)
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.MarkedProgressivelyMeasurable 𝒢 φ :=
  fun t => (h t).mono (prod_le_prod_left (hle t))
omit [MeasurableSpace E] in
/-- A process progressively measurable for a filtration is progressively measurable for its
right-continuous regularisation. -/
theorem progressivelyMeasurable_rightCont {H : Ω → ℝ → ℝ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (h : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ.rightCont H :=
  progressivelyMeasurable_of_le ℱ.le_rightCont h
/-- A marked process progressively measurable for a filtration is progressively measurable for
its right-continuous regularisation. -/
theorem markedProgressivelyMeasurable_rightCont {φ : Ω → ℝ → E → ℝ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.MarkedProgressivelyMeasurable ℱ.rightCont φ :=
  markedProgressivelyMeasurable_of_le ℱ.le_rightCont h
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **The chain data of the arrival times.** For the right-continuous regularisation of a
filtration for which the random measure is Poisson, the arrival times of a measurable mark set
are stopping times, they increase with the index, and the zeroth is the origin. -/
theorem jumpTime_chain_rightCont (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A) :
    (∀ k : ℕ, MeasureTheory.IsStoppingTime ℱ.rightCont
        (LevyStochCalc.Poisson.jumpTime N A k))
      ∧ (∀ (k : ℕ) (ω : Ω), LevyStochCalc.Poisson.jumpTime N A k ω
          ≤ LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
      ∧ ∀ ω : Ω, LevyStochCalc.Poisson.jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  ⟨fun k => LevyStochCalc.Poisson.isStoppingTime_jumpTime_rightCont N A hℱ hA k,
    fun k ω => LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω,
    fun ω => LevyStochCalc.Poisson.jumpTime_zero N A ω⟩
end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

/-- Consecutive arrival times increase. -/
theorem jumpTime_le_jumpTime_succ (k : ℕ) (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A k ω ≤ LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
  LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω
/-- The chain of arrival times starts at the origin. -/
theorem jumpTime_chain_zero (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  LevyStochCalc.Poisson.jumpTime_zero N A ω
/-- The events on which the chain of arrival times has passed the horizon cover almost every
sample point. -/
theorem ae_exists_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ,
      ω ∈ {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'} := by
  filter_upwards [LevyStochCalc.Poisson.ae_jumpTime_chain N A hA hAν T] with ω hω
  exact hω.2
/-- An identity that holds almost everywhere on each event where the chain of arrival times has
passed the horizon holds almost everywhere. -/
theorem ae_eq_of_ae_eq_of_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {L R : Ω → ℝ}
    (h : ∀ m : ℕ, ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
      L ω = R ω) :
    L =ᵐ[P] R :=
  LevyStochCalc.Brownian.Ito.ae_eq_of_ae_eq_on_exhausting
    (S := fun m => {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'})
    (ae_exists_le_jumpTime N A hA hAν T) h
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


