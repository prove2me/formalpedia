-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F001
-- name    : LevyStochCalc_BSDEJ_YoungLipschitz_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:41:58.521837+00:00
-- url     : https://prove2.me/theorems/b62179b9-1409-4161-b420-876d7be9c1b1
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.YoungLipschitz
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.YoungLipschitz. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
import Definitions.Def_SourceProof_8af671222c86fdea87a26691

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

/-- The negated-argument form of `two_mul_mul_generator_sub_le`, as used by the drift pairing
`∫ ω, X s ω * (-Δf) ∂P` in the weighted energy identity. -/
theorem two_mul_mul_generator_sub_le' {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * -(f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  have h := _root_.Prove2MeSourceProof.h_8af671222c86fdea87a26691 hβ hL hlip s y₁ y₂ z₁ z₂ u₁ u₂ hu (-a)
  calc 2 * (a * -(f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      = 2 * (-a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂)) := by ring
    _ ≤ β / 2 * (-a) ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := h
    _ = β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by ring
/-- At the Young weight `β = max 2 (24 * L ^ 2)`, the contraction coefficient `6 * L ^ 2 / β` is
at most `1 / 4` and `β` is itself at least `2`. -/
theorem contraction_factor_le (L : ℝ) :
    6 * L ^ 2 / max 2 (24 * L ^ 2) ≤ 1 / 4 ∧ (2 : ℝ) ≤ max 2 (24 * L ^ 2) := by
  refine ⟨?_, le_max_left _ _⟩
  rcases le_total (24 * L ^ 2) 2 with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    have hL2pos : (0 : ℝ) < L ^ 2 := by linarith
    have h24 : (0 : ℝ) < 24 * L ^ 2 := by linarith
    rw [div_le_div_iff₀ h24 (by norm_num : (0 : ℝ) < 4)]
    nlinarith
end LevyStochCalc.BSDEJ.Contraction


