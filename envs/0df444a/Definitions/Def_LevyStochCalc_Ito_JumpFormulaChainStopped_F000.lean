-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
-- name    : LevyStochCalc_Ito_JumpFormulaChainStopped_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:33:00.795757+00:00
-- url     : https://prove2.me/theorems/ed089c40-f107-460d-b900-e32b45e2f408
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaChainStopped
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaChainStopped. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F001
import Definitions.Def_SourceProof_1c19127385342f00e6ef4903
import Definitions.Def_SourceProof_fd28faada52b5036aa04b1f8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments read along a random vector known at the earlier stopping time

The increment between two ordered stopping times of an integrand built from a path translated by
a random vector known at the earlier time is supported on the region strictly after that time,
where the translation is already known: there the translated path is the path plus the cut-off
vector, which is measurable for the σ-algebra at the running time because the region is a
countable union of rectangles `{σ ≤ q} × (q, t]`. The increment is therefore progressively
measurable without any restriction on the range of the vector or on that of the stopping times.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` — a random vector known at a
  stopping time, cut to the times strictly after it and up to a horizon, is measurable for the
  σ-algebra at that horizon on the product with the time axis.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` — the increment between
  two ordered stopping times of an integrand read along a random vector known at the earlier one
  is progressively measurable.
* `LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift` — that increment has
  measurable uncurrying.
* `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_stopped_sub_cappedJumpSumAt` — the
  increment between consecutive capped arrival times of an integrand read along the capped
  left-limit jump sum is progressively measurable.
* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_stopped_sub_cappedJumpSumAt` — that
  increment has measurable uncurrying.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory

universe u v

section ShiftRegion

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [Zero E]
  {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}

end ShiftRegion

section StoppedShift

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}
  {σ τ : Ω → WithTop ℝ}

/-- The increment between two stopping times of an integrand read along a random vector has
measurable uncurrying. -/
theorem measurable_uncurry_stopped_sub_shift (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {c : Ω → Fin n → ℝ} (hc : Measurable c)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Measurable (Function.uncurry fun ω s => V s ω))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) {K : Ω → ℝ → ℝ}
    (hK : ∀ ω s, K ω s = φ (V s ω + c ω) * H ω s) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s) := by
  refine measurable_uncurry_stopped_sub hσ hτ ?_
  have hfun : Function.uncurry K
      = fun p : Ω × ℝ => φ (V p.2 p.1 + c p.1) * Function.uncurry H p := by
    funext p
    exact hK p.1 p.2
  rw [hfun]
  exact (hφ.measurable.comp (hV.add (hc.comp measurable_fst))).mul hH
end StoppedShift

section FromUnstopped

open scoped NNReal ENNReal

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n d : ℕ} {ℱ : Filtration ℝ mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {chain : ℕ → Ω → WithTop ℝ}
  {V : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ} {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}

/-- An integrand jointly measurable in the sample point and the time has jointly measurable
increments between the members of a chain of stopping times. -/
theorem measurable_uncurry_stopped_sub_chain_of_measurable
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s)) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (chain (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (chain k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s) :=
  fun k p j => measurable_uncurry_stopped_sub (hchain k) (hchain (k + 1)) (hmV k p j)
/-- A progressively measurable integrand has progressively measurable increments between the
members of a chain of stopping times. -/
theorem progressivelyMeasurable_stopped_sub_chain_of_progressivelyMeasurable
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (chain (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (chain k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s :=
  fun k p j => progressivelyMeasurable_stopped_sub (hchain k) (hchain (k + 1)) (hpV k p j)
omit [IsProbabilityMeasure P] in
/-- An integrand of finite energy on every bounded window has increments of finite energy
between the members of a chain of stopping times. -/
theorem energy_stopped_sub_chain_lt_top
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s))
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (V s ω + c k ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Probability.stopped (chain (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (chain k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
  fun k p j => energy_stopped_sub_lt_top (hchain k) (hchain (k + 1)) (hmV k p j) (hqV k p j)
end FromUnstopped

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

open MeasureTheory ProbabilityTheory Filter Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {A : Set E}

/-- The increment between consecutive capped arrival times of an integrand read along the capped
left-limit jump sum is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_cappedJumpSumAt
    (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Probability.ProgressivelyMeasurable ℱ fun ω s => V s ω)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) (k : ℕ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (cappedJumpTime N A T (k + 1))
          (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
            * H ω s) ω s
        - Probability.stopped (cappedJumpTime N A T k)
            (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
              * H ω s) ω s :=
  _root_.Prove2MeSourceProof.h_1c19127385342f00e6ef4903
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k)
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T (k + 1))
    (cappedJumpTime_le_succ N A T k)
    (measurable_cappedJumpSumAt_leftLimPath_of_isStoppingTime X ℱ hℱ hA hfin hXadapt hleft hγ
      (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k))
    hV hφ hH fun _ _ => rfl
/-- The increment between consecutive capped arrival times of an integrand read along the capped
left-limit jump sum has measurable uncurrying. -/
theorem measurable_uncurry_stopped_sub_cappedJumpSumAt
    (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Measurable (Function.uncurry fun ω s => V s ω))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) (T : ℝ) (k : ℕ) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped (cappedJumpTime N A T (k + 1))
          (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
            * H ω s) ω s
        - Probability.stopped (cappedJumpTime N A T k)
            (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
              * H ω s) ω s) :=
  LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k)
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T (k + 1))
    (_root_.Prove2MeSourceProof.h_fd28faada52b5036aa04b1f8 X hA hfin hleft hγ T k) hV hφ hH fun _ _ => rfl
end LevyStochCalc.Ito.JumpFormula


