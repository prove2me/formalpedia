-- Prove2me | Definitions.Def_SourceProof_e554e55fb9c1def6b7e8b55b
-- name    : SourceProof_e554e55fb9c1def6b7e8b55b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:30:22.605529+00:00
-- url     : https://prove2.me/theorems/90b453bc-3862-4f8a-b0c1-470d0fe1f27a
-- title:
--   LevyStochCalc source module: SourceProof_e554e55fb9c1def6b7e8b55b
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy` comes from the `LevyStochCalc.Ito.PicardIntegrandBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_2649fc29ac7d404cbb857b48

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


theorem _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (Z s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  -- the state-zero jump energy, as a function of time
  have hγ0 : Measurable fun s : ℝ => ∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have hj : Measurable fun p : ℝ × E => (‖coeffs.γ p.1 0 p.2‖₊ : ℝ≥0∞) ^ 2 := by
      have : Measurable fun p : ℝ × E => coeffs.γ p.1 0 p.2 :=
        hReg.2.2.1.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
    exact hj.lintegral_prod_right'
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s =>
    _root_.Prove2MeSourceProof.h_2649fc29ac7d404cbb857b48 coeffs hReg hLip s (Z s ω) i) ?_
  have hXi : ∀ i' : Fin n, Measurable fun p : Ω × ℝ => Z p.2 p.1 i' := fun i' =>
    (measurable_pi_apply i').comp
      (hZm.comp (measurable_snd.prodMk measurable_fst))
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (∫⁻ e, (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hγ0.const_mul 2) _
  rw [lintegral_congr hinner, MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · -- the state-zero term: constant in `ω`, finite by `IsRegular`
    rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_lt_top (by simp) (hReg.2.2.2.2.2 T' hT')
  · -- the state term: the frozen process's horizon bound
    have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
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


