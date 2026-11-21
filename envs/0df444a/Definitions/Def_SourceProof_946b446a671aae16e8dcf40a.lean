-- Prove2me | Definitions.Def_SourceProof_946b446a671aae16e8dcf40a
-- name    : SourceProof_946b446a671aae16e8dcf40a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:19:34.098184+00:00
-- url     : https://prove2.me/theorems/6c339332-cd74-436d-b61c-3d752b46648e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F003

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


theorem _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h1 : ENNReal.ofReal (2 * ‖coeffs.μ s 0‖ ^ 2)
        = 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), LevyStochCalc.Ito.Picard.sq_coe_nnnorm,
        ENNReal.ofReal_ofNat]
    have h2 : ENNReal.ofReal (2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2))
        = ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
      rw [show 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)
          = (2 * L ^ 2) * ∑ i', (Z s ω i') ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact congrArg _ (Finset.sum_congr rfl fun i' _ => (LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _).symm)
    calc (‖coeffs.μ s (Z s ω) i‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.μ s (Z s ω) i) ^ 2) := LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal (2 * ‖coeffs.μ s 0‖ ^ 2
            + 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)) :=
          ENNReal.ofReal_le_ofReal (LevyStochCalc.Ito.Picard.sq_mu_le coeffs hLip s _ i)
      _ = 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), h1, h2]
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  have hμ0 : Measurable fun s : ℝ => (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun s : ℝ => coeffs.μ s 0 :=
      hReg.1.comp (measurable_id.prodMk measurable_const)
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hμ0.const_mul 2) _
  rw [lintegral_congr hinner, MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_lt_top (by simp) (hReg.2.2.2.1 T' hT')
  · have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (2 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun ω => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr hconst,
      MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * L ^ 2) ≠ ⊤)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hZsq T'
end LevyStochCalc.Ito.Picard


