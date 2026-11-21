-- Prove2me | Definitions.Def_SourceProof_be1408ec5fbfc50e70ae1572
-- name    : SourceProof_be1408ec5fbfc50e70ae1572
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:19:27.021187+00:00
-- url     : https://prove2.me/theorems/2b888c26-5f8c-4c55-8403-8a6d724b888f
-- title:
--   LevyStochCalc source module: SourceProof_be1408ec5fbfc50e70ae1572
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.cross_increment_integrable` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_be1408ec5fbfc50e70ae1572
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (hab₁ : a₁ ≤ b₁) (ha₂ : 0 ≤ a₂) (hab₂ : a₂ ≤ b₂)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁meas : Measurable ξ₁) (hξ₂meas : Measurable ξ₂)
    (M₁ : ℝ) (hbd₁ : ∀ ω, |ξ₁ ω| ≤ M₁) (M₂ : ℝ) (hbd₂ : ∀ ω, |ξ₂ ω| ≤ M₂) :
    MeasureTheory.Integrable
      (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) P := by
  have h_meas₁ : Measurable (fun ω => W.W b₁ ω - W.W a₁ ω) :=
    (W.measurable_eval b₁).sub (W.measurable_eval a₁)
  have h_meas₂ : Measurable (fun ω => W.W b₂ ω - W.W a₂ ω) :=
    (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have sq_int : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      MeasureTheory.Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h_eq | h_lt
    · rw [show (fun ω => (W.W b ω - W.W a ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; rw [← h_eq]; ring]
      exact MeasureTheory.integrable_const 0
    · exact LevyStochCalc.Brownian.Ito.increment_sq_integrable W ha h_lt
  have h_int_i_sq := sq_int ha₁ hab₁
  have h_int_j_sq := sq_int ha₂ hab₂
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1 / 2 : ℝ))
        (h_int_j_sq.const_mul (1 / 2 : ℝ))) (h_meas₁.mul h_meas₂).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have h : |W.W b₁ ω - W.W a₁ ω| * |W.W b₂ ω - W.W a₂ ω|
        ≤ (1 / 2) * (W.W b₁ ω - W.W a₁ ω) ^ 2 + (1 / 2) * (W.W b₂ ω - W.W a₂ ω) ^ 2 := by
      nlinarith [sq_abs (W.W b₁ ω - W.W a₁ ω), sq_abs (W.W b₂ ω - W.W a₂ ω),
        sq_nonneg (|W.W b₁ ω - W.W a₁ ω| - |W.W b₂ ω - W.W a₂ ω|)]
    exact h
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => (ξ₁ ω * ξ₂ ω)
            * ((W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) from by funext ω; ring]
  refine MeasureTheory.Integrable.bdd_mul (c := |M₁| * |M₂|) h_int_ΔW
    (hξ₁meas.mul hξ₂meas).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hbd₁ ω) (le_abs_self _)) (le_trans (hbd₂ ω) (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)
end LevyStochCalc.Brownian.Ito


