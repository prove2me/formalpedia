-- Prove2me | Definitions.Def_SourceProof_1a2c983c4a1fa7387543aefa
-- name    : SourceProof_1a2c983c4a1fa7387543aefa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:08.651176+00:00
-- url     : https://prove2.me/theorems/a99175fb-9435-42d4-a0c3-9a22137472dd
-- title:
--   LevyStochCalc source module: SourceProof_1a2c983c4a1fa7387543aefa
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq` comes from the `LevyStochCalc.Ito.PicardStochasticLipschitz` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Lipschitz estimates for the stochastic components of the Picard map

The `L²`-isometry `𝔼|∫_0^T H₁ dW - ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁ - H₂|² ds` for the difference of
two Brownian Itô integrals, the discrete Cauchy-Schwarz inequality and the `ℝ≥0∞` norm-square
identities it is combined with, and the resulting per-component `L²` Lipschitz bounds for the
diffusion and the jump component of the Picard map in terms of the Lipschitz constants of `σ` and
`γ`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_1a2c983c4a1fa7387543aefa
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {d : ℕ} (M : Fin d → Ω → ℝ)
    (hM : ∀ j : Fin d, Measurable (M j)) :
    ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Pointwise: ENNReal.ofReal((∑ M_j ω)²) ≤ ENNReal.ofReal(d * ∑ M_j ω²)
  --                                         = d · ∑ ENNReal.ofReal(M_j ω²)
  have h_cs_ofReal : ∀ ω : Ω,
      ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2)
        ≤ ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2) := by
    intro ω
    have h_sum_sq : (∑ j : Fin d, M j ω) ^ 2
        ≤ (d : ℝ) * ∑ j : Fin d, (M j ω) ^ 2 :=
      LevyStochCalc.Ito.Picard.sum_sq_le_card_mul_sum_sq_real (fun j => M j ω)
    have h_d_nn : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have h_each_nn : ∀ j : Fin d, 0 ≤ (M j ω) ^ 2 := fun j => sq_nonneg _
    have h_sum_inner_nn : 0 ≤ ∑ j : Fin d, (M j ω) ^ 2 :=
      Finset.sum_nonneg (fun j _ => h_each_nn j)
    calc ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2)
        ≤ ENNReal.ofReal ((d : ℝ) * ∑ j : Fin d, (M j ω) ^ 2) :=
            ENNReal.ofReal_le_ofReal h_sum_sq
      _ = ENNReal.ofReal ((d : ℝ)) * ENNReal.ofReal (∑ j : Fin d, (M j ω) ^ 2) :=
            ENNReal.ofReal_mul h_d_nn
      _ = ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h_each_nn j)]
  -- Rewrite the LHS to the ofReal form via nnnorm_sq_real.
  have h_LHS_ofReal : ∀ ω : Ω,
      (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2) :=
    fun ω => LevyStochCalc.Ito.Picard.ennreal_nnnorm_sq_real _
  -- Per-j rewrite: (‖M_j ω‖₊ : ℝ≥0∞)² = ENNReal.ofReal((M_j ω)²)
  have h_per_j_ofReal : ∀ ω : Ω, ∀ j : Fin d,
      (‖M j ω‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((M j ω) ^ 2) :=
    fun ω j => LevyStochCalc.Ito.Picard.ennreal_nnnorm_sq_real _
  -- Pull together the pointwise bound:
  have h_pt : ∀ ω : Ω,
      (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω
    rw [h_LHS_ofReal ω]
    refine (h_cs_ofReal ω).trans ?_
    rw [show ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2)
          = ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_per_j_ofReal ω j]]
  -- Now take the lintegral.
  calc ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((d : ℝ)) *
          ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_mono h_pt
    _ = ENNReal.ofReal ((d : ℝ)) *
        ∫⁻ ω, ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((d : ℝ)) *
        ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        congr 1
        rw [MeasureTheory.lintegral_finsetSum]
        intro j _
        exact ((hM j).enorm).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [ENNReal.ofReal_natCast]
end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard


