-- Prove2me | Definitions.Def_SourceProof_388a40baa407d0b0ae15b23c
-- name    : SourceProof_388a40baa407d0b0ae15b23c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:31:55.241317+00:00
-- url     : https://prove2.me/theorems/2759946a-7a6c-4b7f-8fef-e52149df14d3
-- title:
--   LevyStochCalc source module: SourceProof_388a40baa407d0b0ae15b23c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Stability.lintegral_sq_sub_marked_lt_top` comes from the `LevyStochCalc.Ito.StabilityEstimate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted stability estimates for Itô–Lévy processes

The difference of two Itô–Lévy processes over the same Lévy driver and filtration is again an
Itô–Lévy process, with the differenced data (`isItoLevyProcess_sub`). Feeding it to the
exponentially weighted second-moment identity turns a bound on the rate

`2 𝔼[ΔX_s Δb_s] + ∑_j 𝔼[|Δσ_j(s)|²] + 𝔼 ∫_E |Δγ(s, e)|² ν(de) ≤ c 𝔼[|ΔX_s|²]`

into the stability estimate `𝔼[|ΔX_T|²] ≤ e^{cT} 𝔼[|ΔX₀|²]`, with no Grönwall lemma: the
exponential weight does the work. A drift, diffusion and jump coefficient Lipschitz in the state
gives such a rate bound with `c = 2L + 2L²`, and equal initial values then force the two
processes to agree at the horizon.

## Main statements

* `integral_mul_self_le_of_rate_le` — the weighted identity as a bound: a rate bounded by
  `c 𝔼[X_s²]` at almost every time of the window gives `𝔼[X_T²] ≤ e^{cT} 𝔼[X₀²]`.
* `isItoLevyProcess_sub` — the difference of two Itô–Lévy processes over the same driver is an
  Itô–Lévy process with the differenced initial value, drift, diffusion and jump coefficient.
* `integral_sub_mul_self_le_of_rate_le` — the stability estimate under a rate bound on the
  difference.
* `integral_sub_mul_self_le_of_lipschitz` — the stability estimate under pointwise Lipschitz
  bounds on the differences of the coefficients, with `c = 2L + 2L²`.
* `ae_eq_of_lipschitz_of_ae_eq_initial` — two Itô–Lévy processes with Lipschitz-close
  coefficients and almost surely equal initial values agree almost surely at every horizon.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Stability

open LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section RateBound

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end RateBound

section Difference

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c [SFinite P] {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) {T : ℝ}
    (hφq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  rw [← LevyStochCalc.Ito.SecondMoment.lintegral_prod_marked (P := P) (ν := ν) (hφ.sub hψ) T]
  rw [← LevyStochCalc.Ito.SecondMoment.lintegral_prod_marked (P := P) (ν := ν) hφ T] at hφq
  rw [← LevyStochCalc.Ito.SecondMoment.lintegral_prod_marked (P := P) (ν := ν) hψ T] at hψq
  have hmφ : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hφ.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hmψ : Measurable fun p : Ω × ℝ × E => (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hψ.nnnorm.coe_nnreal_ennreal.pow_const 2
  calc ∫⁻ p, (‖φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
        ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      ≤ ∫⁻ p, 2 * ((‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 + (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2)
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :=
        lintegral_mono fun p => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _
    _ = 2 * ((∫⁻ p, (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)))
        + ∫⁻ p, (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))) := by
        have hmsum : Measurable fun p : Ω × ℝ × E =>
            (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 + (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
          hmφ.add hmψ
        rw [lintegral_const_mul _ hmsum]
        congr 1
        exact lintegral_add_left hmφ _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨hφq, hψq⟩)
variable {d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

end Difference

section Stability

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

end Stability

end LevyStochCalc.Ito.Stability


