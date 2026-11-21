-- Prove2me | Definitions.Def_SourceProof_55e10c2bb5834f5a3716267c
-- name    : SourceProof_55e10c2bb5834f5a3716267c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:19:59.946644+00:00
-- url     : https://prove2.me/theorems/180f9c46-4905-4ab9-8473-480630236487
-- title:
--   LevyStochCalc source module: SourceProof_55e10c2bb5834f5a3716267c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.itoIntegral_congr_ae` comes from the `LevyStochCalc.Ito.PicardLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8

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


theorem _root_.Prove2MeSourceProof.h_55e10c2bb5834f5a3716267c
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8
    Wj ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ ht
  rw [LevyStochCalc.Ito.Picard.lintegral_sq_sub_eq_zero_of_ae H₁ H₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t).sub
      (LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice Wj ℱ hℱ H₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have : (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using this
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


