-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
-- name    : LevyStochCalc_Ito_PicardLocality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:14:29.723605+00:00
-- url     : https://prove2.me/theorems/486046da-1729-4c75-b1e5-636f4a9bd33e
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardLocality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardLocality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSupL2_F000

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

/-- The Itô integral against a Brownian motion is measurable at each time. -/
theorem measurable_itoIntegral_slice
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H hm hp hs t ω := by
  obtain ⟨Filt, hMart⟩ :=
    LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral Wj ℱ hℱ H hm hp hs
  exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
/-- The compensated-Poisson integral is measurable at each time. -/
theorem measurable_compensatedIntegral_slice {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ hm hp hs t ω :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN φ hm hp hs
    t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl
/-! ### An a.e. vanishing integrand has an a.e. vanishing energy -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem lintegral_sq_sub_eq_zero_of_ae {t : ℝ} (H₁ H₂ : Ω → ℝ → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]
omit [IsProbabilityMeasure P] in
/-- The mark-indexed `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem lintegral_sq_sub_mark_eq_zero_of_ae {ν : Measure E} {t : ℝ} (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]
/-! ### Locality of the two stochastic integrals -/

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


