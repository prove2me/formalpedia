-- Prove2me | Definitions.Def_SourceProof_2649fc29ac7d404cbb857b48
-- name    : SourceProof_2649fc29ac7d404cbb857b48
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:26:47.49563+00:00
-- url     : https://prove2.me/theorems/85dd59f4-4290-44a7-990f-27064f375a45
-- title:
--   LevyStochCalc source module: SourceProof_2649fc29ac7d404cbb857b48
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_gamma_le` comes from the `LevyStochCalc.Ito.PicardIntegrandBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_2649fc29ac7d404cbb857b48 {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∫⁻ e, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 := by
  have hγ0 : Measurable fun e : E => (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun e : E => coeffs.γ s 0 e :=
      hReg.2.2.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  -- pointwise: split off the value at the state `0`
  have hpt : ∀ e : E, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
        + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
    intro e
    have hb : |coeffs.γ s 0 e i| ≤ ‖coeffs.γ s 0 e‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (coeffs.γ s 0 e) i
    have hd : |coeffs.γ s x e i - coeffs.γ s 0 e i|
        ≤ ‖coeffs.γ s x e - coeffs.γ s 0 e‖ := by
      simpa [Real.norm_eq_abs, Pi.sub_apply]
        using norm_le_pi_norm (coeffs.γ s x e - coeffs.γ s 0 e) i
    have hreal : (coeffs.γ s x e i) ^ 2
        ≤ 2 * ‖coeffs.γ s 0 e‖ ^ 2 + 2 * ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2 := by
      have h1 : (coeffs.γ s 0 e i) ^ 2 ≤ ‖coeffs.γ s 0 e‖ ^ 2 := by
        nlinarith [abs_nonneg (coeffs.γ s 0 e i), sq_abs (coeffs.γ s 0 e i), norm_nonneg
          (coeffs.γ s 0 e)]
      have h2 : (coeffs.γ s x e i - coeffs.γ s 0 e i) ^ 2
          ≤ ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2 := by
        nlinarith [abs_nonneg (coeffs.γ s x e i - coeffs.γ s 0 e i),
          sq_abs (coeffs.γ s x e i - coeffs.γ s 0 e i),
          norm_nonneg (coeffs.γ s x e - coeffs.γ s 0 e)]
      nlinarith [sq_nonneg (coeffs.γ s x e i - 2 * coeffs.γ s 0 e i)]
    calc (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.γ s x e i) ^ 2) := LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal (2 * ‖coeffs.γ s 0 e‖ ^ 2
            + 2 * ‖coeffs.γ s x e - coeffs.γ s 0 e‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
            ← LevyStochCalc.Ito.Picard.sq_coe_nnnorm, ← LevyStochCalc.Ito.Picard.sq_coe_nnnorm]
  -- the Lipschitz clause, converted to the sum of squares
  have hLbound : 2 * ∫⁻ e, (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 := by
    refine (mul_le_mul' le_rfl (hLip.2.2.2 s x 0)).trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      show (2 : ℝ) * (L ^ 2 * ‖x - 0‖ ^ 2) = (2 * L ^ 2) * ‖x‖ ^ 2 by rw [sub_zero]; ring,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2)]
    exact mul_le_mul' le_rfl (LevyStochCalc.Ito.Picard.ofReal_sq_norm_le_sum x)
  calc ∫⁻ e, (‖coeffs.γ s x e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ e, (2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2) ∂ν := lintegral_mono hpt
    _ = (∫⁻ e, 2 * (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ∫⁻ e, 2 * (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
        MeasureTheory.lintegral_add_left (hγ0.const_mul 2) _
    _ = 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + 2 * ∫⁻ e, (‖coeffs.γ s x e - coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖x i'‖₊ : ℝ≥0∞) ^ 2 :=
        add_le_add le_rfl hLbound
end LevyStochCalc.Ito.Picard


