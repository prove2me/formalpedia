-- Prove2me | Definitions.Def_SourceProof_36f7727cdf4c604558c9da84
-- name    : SourceProof_36f7727cdf4c604558c9da84
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:29.432203+00:00
-- url     : https://prove2.me/theorems/d3d88859-0c30-4e02-b26b-a131d08a2956
-- title:
--   LevyStochCalc source module: SourceProof_36f7727cdf4c604558c9da84
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_markIntegral` comes from the `LevyStochCalc.Ito.JumpSplitting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F003
import Definitions.Def_LevyStochCalc_Ito_Setting_F000
import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)


theorem _root_.Prove2MeSourceProof.h_36f7727cdf4c604558c9da84 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {φ : Ω → ℝ → E → ℝ} (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => ∫ e in A, φ ω s e ∂ν := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun r : (Ω × ℝ) × E =>
      (Set.Iic t).indicator (fun s => φ r.1.1 s r.2) r.1.2 :=
    (h t).comp_measurable MeasurableEquiv.prodAssoc.measurable
  have h2 : StronglyMeasurable fun p : Ω × ℝ =>
      ∫ e in A, (Set.Iic t).indicator (fun s => φ p.1 s e) p.2 ∂ν :=
    h1.integral_prod_right' (ν := ν.restrict A)
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => ∫ e in A, φ p.1 s e ∂ν) p.2)
      = fun p : Ω × ℝ => ∫ e in A, (Set.Iic t).indicator (fun s => φ p.1 s e) p.2 ∂ν := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, integral_zero]
  rw [key]
  exact h2
end Regularity

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


