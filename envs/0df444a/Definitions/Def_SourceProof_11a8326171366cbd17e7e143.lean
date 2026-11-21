-- Prove2me | Definitions.Def_SourceProof_11a8326171366cbd17e7e143
-- name    : SourceProof_11a8326171366cbd17e7e143
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:11.698219+00:00
-- url     : https://prove2.me/theorems/fa7000d0-944c-4430-b12f-37ba9a76b54f
-- title:
--   LevyStochCalc source module: SourceProof_11a8326171366cbd17e7e143
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top` comes from the `LevyStochCalc.Ito.PicardSupL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSupL2_F000
import Definitions.Def_SourceProof_06ce725b2f140e9df5ff737b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` bound for the Picard step

`LevyStochCalc.Ito.Setting.JumpDiffusion.sup_L2` asks for `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`, the `S²`
norm, which is stronger than the weighted supremum of `L²` norms the Picard space carries. The
Picard step splits into a drift, `d` Brownian integrals and a compensated-Poisson integral; the
drift is bounded pathwise by its own total variation over the window, and each stochastic
component is a martingale, so Doob's `L²` inequality over the dyadic points applies. Only the
dyadic form of Doob is available here, because the stochastic integrals are càdlàg only up to
modification.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### An elementary two-term bound -/

/-! ### The drift component -/

/-! ### The stochastic components -/

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-! ### The whole step -/


theorem _root_.Prove2MeSourceProof.h_11a8326171366cbd17e7e143
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set A : ℝ → Ω → ℝ := fun t ω => LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i with hA
  set B : ℝ → Ω → ℝ := fun t ω =>
    LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i with hB
  set C : ℝ → Ω → ℝ := fun t ω =>
    LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i with hC
  have hunfold : (fun t (ω : Ω) =>
      LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i)
      = fun t ω => A t ω + B t ω + C t ω := rfl
  have hAm : ∀ t : ℝ, Measurable (A t) := fun t =>
    LevyStochCalc.Ito.Picard.measurable_picardStep_drift coeffs X x₀ i (hμm i) t
  have hBm : ∀ t : ℝ, Measurable (B t) := fun t =>
    _root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i t
  have hCm : ∀ t : ℝ, Measurable (C t) := fun t =>
    LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i t
  have hsupm : ∀ (D : ℝ → Ω → ℝ), (∀ t, Measurable (D t)) →
      Measurable fun ω => (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax D T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun D hD => (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax hD T' m).pow_const 2
  -- the drift is dominated pathwise
  have hAfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_)
      (LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top coeffs X x₀ i hT'.le (hμm i) (hμsq i T' hT'))
    filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq (P := P) (hμm i) (hμsq i)] with ω hω
    exact pow_le_pow_left' (LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le coeffs X x₀ i hT'.le (hω T')) 2
  have hBfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ :=
    LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i hT'
  have hCfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_sq_iSup_jump_le N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas
      h_γ_sq i hT'.le) ?_
    exact ENNReal.mul_lt_top (by norm_num) (h_γ_sq i T' hT')
  rw [hunfold]
  calc ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => A t ω + B t ω + C t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, (16 : ℝ≥0∞) * ((⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans (pow_le_pow_left' (le_trans
          (LevyStochCalc.Probability.iSup_dyadicRunMax_add_le (fun t ω => A t ω + B t ω) C T' ω)
          (add_le_add (LevyStochCalc.Probability.iSup_dyadicRunMax_add_le A B T' ω) le_rfl)) 2)
          (LevyStochCalc.Ito.Picard.sq_add3_le_sixteen_mul _ _ _)
    _ < ⊤ := by
        have hAB : Measurable fun ω : Ω => (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
            + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 := (hsupm A hAm).add (hsupm B hBm)
        rw [lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤),
          lintegral_add_left hAB, lintegral_add_left (hsupm A hAm)]
        exact ENNReal.mul_lt_top (by norm_num)
          (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩, hCfin⟩)
/-! ### The `S²` bound for the raw self-map -/

end LevyStochCalc.Ito.Picard


