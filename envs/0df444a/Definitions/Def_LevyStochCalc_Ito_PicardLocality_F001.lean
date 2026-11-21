-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardLocality_F001
-- name    : LevyStochCalc_Ito_PicardLocality_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:23:44.004978+00:00
-- url     : https://prove2.me/theorems/7326d48e-b1a9-4ce3-874d-5d4a72e525db
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardLocality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardLocality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSupL2_F000
import Definitions.Def_SourceProof_55e10c2bb5834f5a3716267c
import Definitions.Def_SourceProof_cda07e33f55ed24b65eb1212

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

omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The drift component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_drift_congr_ae {t : ℝ}
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P, picardStep_drift coeffs X x₀ t ω = picardStep_drift coeffs Y x₀ t ω := by
  filter_upwards [hXY] with ω hω
  have hω' : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) t → X s ω = Y s ω :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : (fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
      = fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Y s ω) i := by
    funext i
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω'] with s hs hsmem
    rw [hs hsmem]
  simp only [picardStep_drift, hint]
omit [MeasurableSpace E] in
/-- The Brownian component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_diffusion_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
        = picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω := by
  have hcomp : ∀ p : Fin n × Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
          (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
          (h_σ_meas_X p.1 p.2) (h_σ_progMeas_X p.1 p.2) (h_σ_sq_X p.1 p.2) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
          (fun ω' s => coeffs.σ s (Y s ω') p.1 p.2)
          (h_σ_meas_Y p.1 p.2) (h_σ_progMeas_Y p.1 p.2) (h_σ_sq_Y p.1 p.2) t ω := by
    rintro ⟨i, j⟩
    refine _root_.Prove2MeSourceProof.h_55e10c2bb5834f5a3716267c (W.W j) ℱ (hℱW j) _ _ _ _ _ _ _ _ ht ?_
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  funext i
  simp only [picardStep_diffusion]
  exact Finset.sum_congr rfl fun j _ => hω (i, j)
/-- The compensated-Poisson component at `t` only reads its input on `[0, t]`. -/
theorem picardStep_jump_congr_ae
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  have hcomp : ∀ i : Fin n, ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (X s ω') e i)
          (h_γ_meas_X i) (h_γ_progMeas_X i) (h_γ_sq_X i) t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (Y s ω') e i)
          (h_γ_meas_Y i) (h_γ_progMeas_Y i) (h_γ_sq_Y i) t ω := by
    intro i
    refine _root_.Prove2MeSourceProof.h_cda07e33f55ed24b65eb1212 N ℱ hℱN _ _ _ _ _ _ _ _ ht ?_
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with s hs
    funext e
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  funext i
  exact hω i
/-- **The Picard step is local.** Inputs agreeing a.e. on `[0, t]` give a.e. equal steps at `t`. -/
theorem picardStep_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  filter_upwards [picardStep_drift_congr_ae coeffs X Y x₀ hXY,
    picardStep_diffusion_congr_ae W ℱ hℱW coeffs X Y h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y ht hXY,
    picardStep_jump_congr_ae N ℱ hℱN coeffs X Y h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht hXY] with ω h1 h2 h3
  simp only [picardStep, h1, h2, h3]
end Step

end LevyStochCalc.Ito.Picard


