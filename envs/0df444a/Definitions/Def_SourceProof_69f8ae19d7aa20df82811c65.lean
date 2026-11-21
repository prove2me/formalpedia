-- Prove2me | Definitions.Def_SourceProof_69f8ae19d7aa20df82811c65
-- name    : SourceProof_69f8ae19d7aa20df82811c65
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:00:48.564506+00:00
-- url     : https://prove2.me/theorems/af9b7c5e-7271-4603-86f2-d86e5bbc2b5a
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction estimate

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon, so
the estimate transfers to `picardStepOnStop`, from there through the modification
`picardSelfMap_ae_eq` to `picardSelfMap` itself, and in the same way to the step taken against a
raw state process. The iterates `picardIter` of the self-map are consequently geometrically
Bielecki-Cauchy, and at a weight making the contraction rate `< 1` they converge to
`bieleckiLimit`.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
* `bieleckiNorm_picardIter_sub_bieleckiLimit_le` — the iterates converge to `bieleckiLimit`.
* `bieleckiNorm_picardStepOnStop_sub_rawStop_le` — the estimate against a raw state process.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_69f8ae19d7aa20df82811c65 {Z₁ Z₂ : ℝ → Ω → (Fin n → ℝ)}
    (hm₁ : Measurable (Function.uncurry Z₁)) (hm₂ : Measurable (Function.uncurry Z₂))
    (h₁ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h₂ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω : Ω, ∀ s : ℝ, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    refine (LevyStochCalc.Ito.Picard.sq_nnnorm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul' le_rfl (by rw [LevyStochCalc.Ito.Picard.sq_coe_nnnorm]; exact LevyStochCalc.Ito.Picard.ofReal_sq_norm_le_sum _)
    · exact mul_le_mul' le_rfl (by rw [LevyStochCalc.Ito.Picard.sq_coe_nnnorm]; exact LevyStochCalc.Ito.Picard.ofReal_sq_norm_le_sum _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = 2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [lintegral_add_left ((LevyStochCalc.Ito.Picard.measurable_sq_slice_time hm₁ ω).const_mul 2),
      lintegral_const_mul _ (LevyStochCalc.Ito.Picard.measurable_sq_slice_time hm₁ ω),
      lintegral_const_mul _ (LevyStochCalc.Ito.Picard.measurable_sq_slice_time hm₂ ω)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
          (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2
            + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_congr fun ω => hinner ω
    _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [lintegral_add_left ((LevyStochCalc.Ito.Picard.measurable_lintegral_sq hm₁ b).const_mul 2),
          lintegral_const_mul _ (LevyStochCalc.Ito.Picard.measurable_lintegral_sq hm₁ b),
          lintegral_const_mul _ (LevyStochCalc.Ito.Picard.measurable_lintegral_sq hm₂ b)]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (h₁ b),
        ENNReal.mul_lt_top (by norm_num) (h₂ b)⟩
/-! ### The contraction estimate for the step and the self-map -/

/-! ### The Picard iterates and their limit -/

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The limit of the iterates -/

/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


