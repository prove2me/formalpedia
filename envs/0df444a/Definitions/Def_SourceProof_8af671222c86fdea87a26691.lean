-- Prove2me | Definitions.Def_SourceProof_8af671222c86fdea87a26691
-- name    : SourceProof_8af671222c86fdea87a26691
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:31.309928+00:00
-- url     : https://prove2.me/theorems/e8d42312-8945-4547-8183-a703236d153f
-- title:
--   LevyStochCalc source proof: LevyStochCalc.BSDEJ.Contraction.two_mul_mul_generator_sub_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_99da3ce4a2e20155bfe0bf4c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Young and Lipschitz pointwise rate bounds for a BSDEJ generator

Pure real-variable inequalities behind the BSDEJ contraction estimate: a weighted Young
inequality (`two_mul_mul_le_young`), a three-term square bound (`sq_add_add_le_three`), a bound
of the `Fin d → ℝ` sup norm by the sum of squared coordinates (`sq_norm_pi_le_sum_sq`), their
combination into a pointwise bound on the squared increment of a Lipschitz generator
(`sq_generator_sub_le`) and on `2 * (a * Δf)` for that increment (`two_mul_mul_generator_sub_le`
and its negated-argument form `two_mul_mul_generator_sub_le'`), and the contraction threshold on
the Young weight `β = max 2 (24 * L ^ 2)` (`contraction_factor_le`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Contraction

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ν : Measure E}
variable {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}


theorem _root_.Prove2MeSourceProof.h_8af671222c86fdea87a26691 {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  have hyoung := LevyStochCalc.BSDEJ.Contraction.two_mul_mul_le_young hβ a (f s y₁ z₁ u₁ - f s y₂ z₂ u₂)
  have hsq := _root_.Prove2MeSourceProof.h_99da3ce4a2e20155bfe0bf4c hL hlip s y₁ y₂ z₁ z₂ u₁ u₂ hu
  have hβnn : (0 : ℝ) ≤ 2 / β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hβnn
  have heq : 2 / β * (3 * L ^ 2 *
        ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal))
      = 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
    ring
  linarith [hyoung, hmul, heq]
end LevyStochCalc.BSDEJ.Contraction


