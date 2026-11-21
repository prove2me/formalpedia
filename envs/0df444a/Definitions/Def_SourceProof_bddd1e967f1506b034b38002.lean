-- Prove2me | Definitions.Def_SourceProof_bddd1e967f1506b034b38002
-- name    : SourceProof_bddd1e967f1506b034b38002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:32:48.161531+00:00
-- url     : https://prove2.me/theorems/be9b423e-4b8b-4448-9444-3bd0511e0557
-- title:
--   LevyStochCalc source module: SourceProof_bddd1e967f1506b034b38002
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegral` comes from the `LevyStochCalc.Ito.SecondMomentQuadratic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_bddd1e967f1506b034b38002 (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hψp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, φ ω s e * ψ ω s e ∂ν ∂volume ∂P := by
  have hU2 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hV2 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hUV2 : MemLp (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) 2 P :=
    hU2.sub hV2
  have hdiff := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm
    hφp hψp hφq hψq T hT
  have hdq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    rw [← hdiff]
    exact LevyStochCalc.Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hUV2
  have hφ2 := LevyStochCalc.Ito.SecondMoment.memLp_two_prod_marked hφm (hφq T hT)
  have hψ2 := LevyStochCalc.Ito.SecondMoment.memLp_two_prod_marked hψm (hψq T hT)
  have hUU : ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω ∂P
      = ∫ p, φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hU2,
      LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ hφm hφp hφq T hT]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_marked_eq hφm (hφq T hT)
  have hVV : ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω ∂P
      = ∫ p, ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hV2,
      LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T hT]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_marked_eq hψm (hψq T hT)
  have hDD : ∫ ω, (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
        * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) ∂P
      = ∫ p, (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) * (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2)
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hUV2, hdiff]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_marked_eq (φ := fun ω s e => φ ω s e - ψ ω s e) (hφm.sub hψm) hdq
  have iUU : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω) P :=
    hU2.integrable_mul hU2
  have iVV : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) P :=
    hV2.integrable_mul hV2
  have iDD : Integrable (fun ω =>
      (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
      * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)) P :=
    hUV2.integrable_mul hUV2
  have iS : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) P :=
    iUU.add iVV
  have hexp : (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
      = fun ω =>
        (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
          * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        - (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
        * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω))
        / 2 := by
    funext ω
    ring
  have iφφ : Integrable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hφ2.integrable_mul hφ2
  have iψψ : Integrable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hψ2.integrable_mul hψ2
  have iφψ : Integrable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hφ2.integrable_mul hψ2
  have iDD' : Integrable (fun p : Ω × ℝ × E =>
      (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) * (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2))
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :=
    (hφ2.sub hψ2).integrable_mul (hφ2.sub hψ2)
  have iS' : Integrable (fun p : Ω × ℝ × E =>
      φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2 + ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := iφφ.add iψψ
  rw [hexp, integral_div, integral_sub iS iDD, integral_add iUU iVV, hUU, hVV, hDD,
    ← integral_add iφφ iψψ, ← integral_sub iS' iDD', ← integral_div, ← LevyStochCalc.Ito.SecondMoment.integral_prod_marked iφψ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring
end PolarisedMarked

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Augmented

end LevyStochCalc.Ito.SecondMoment


