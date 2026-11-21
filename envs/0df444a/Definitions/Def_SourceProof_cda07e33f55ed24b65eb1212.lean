-- Prove2me | Definitions.Def_SourceProof_cda07e33f55ed24b65eb1212
-- name    : SourceProof_cda07e33f55ed24b65eb1212
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:59.881046+00:00
-- url     : https://prove2.me/theorems/7c2230ba-1602-468f-ad50-b6722b33460f
-- title:
--   LevyStochCalc source module: SourceProof_cda07e33f55ed24b65eb1212
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae` comes from the `LevyStochCalc.Ito.PicardLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Locality of the Picard step

The Picard step at time `t` reads its input only on `[0, t]`: the drift is a Bochner integral
over `Set.Icc 0 t`, and the two stochastic components are `L²` integrals whose difference
isometries turn an a.e. vanishing integrand into an a.e. vanishing integral. Consequently two
input paths agreeing `volume ⊗ P`-a.e. on `[0, t]` produce a.e. equal steps at `t`, which is
what identifies a window solution with the solution on any longer window.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Slice measurability of the two stochastic integrals -/

/-! ### An a.e. vanishing integrand has an a.e. vanishing energy -/

/-! ### Locality of the two stochastic integrals -/


theorem _root_.Prove2MeSourceProof.h_cda07e33f55ed24b65eb1212 {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
    N ℱ hℱN φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ t ht
  rw [LevyStochCalc.Ito.Picard.lintegral_sq_sub_mark_eq_zero_of_ae (ν := ν) φ₁ φ₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t).sub
      (LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice N ℱ hℱN φ₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have hz : (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
        : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
/-! ### Locality of the Picard step -/

section Step

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)

end Step

end LevyStochCalc.Ito.Picard


