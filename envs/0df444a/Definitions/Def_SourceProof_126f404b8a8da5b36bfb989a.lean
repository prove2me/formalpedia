-- Prove2me | Definitions.Def_SourceProof_126f404b8a8da5b36bfb989a
-- name    : SourceProof_126f404b8a8da5b36bfb989a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:53:22.0291+00:00
-- url     : https://prove2.me/theorems/2c89e245-718e-43b2-9a72-1cc7637bf4e7
-- title:
--   LevyStochCalc source module: SourceProof_126f404b8a8da5b36bfb989a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_add_setIntegral` comes from the `LevyStochCalc.Ito.SecondMomentWeighted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F001
import Definitions.Def_SourceProof_d8b446e22164b7620e52d72e
import Definitions.Def_SourceProof_f574d7521b7b37d4f4a7a428

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_126f404b8a8da5b36bfb989a
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, X t ω * X t ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) t, (2 * ∫ ω, X s ω * b s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  have i1 : Integrable (fun s => 2 * ∫ ω, X s ω * b s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (_root_.Prove2MeSourceProof.h_d8b446e22164b7620e52d72e h hX₀2 hbm hbp hbq ht).const_mul 2
  have iσ : ∀ j : Fin d, Integrable (fun s => (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := fun j =>
    LevyStochCalc.Ito.SecondMoment.integrableOn_toReal_lintegral (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_sq_diffusion h j) (h.σ_sq j t ht)
  have i2 : Integrable (fun s => ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := integrable_finsetSum _ fun j _ => iσ j
  have i12 : Integrable (fun s => 2 * ∫ ω, X s ω * b s ω ∂P
      + ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := i1.add i2
  have i3 : Integrable (fun s => (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    LevyStochCalc.Ito.SecondMoment.integrableOn_toReal_lintegral (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump h) (h.γ_sq t ht)
  rw [_root_.Prove2MeSourceProof.h_f574d7521b7b37d4f4a7a428 h 𝒲 hX₀ hX₀2 hbm hbp hbq ht,
    integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_finsetSum _ fun j _ => iσ j,
    LevyStochCalc.Ito.SecondMoment.toReal_lintegral_lintegral_eq (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump h) (h.γ_sq t ht),
    Finset.sum_congr rfl fun j _ =>
      LevyStochCalc.Ito.SecondMoment.toReal_lintegral_lintegral_eq (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_sq_diffusion h j) (h.σ_sq j t ht)]
  ring
end Weighted

section WeightedVector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end AugmentedMore

end LevyStochCalc.Ito.SecondMoment


