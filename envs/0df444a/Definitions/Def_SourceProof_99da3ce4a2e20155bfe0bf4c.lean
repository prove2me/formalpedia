-- Prove2me | Definitions.Def_SourceProof_99da3ce4a2e20155bfe0bf4c
-- name    : SourceProof_99da3ce4a2e20155bfe0bf4c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:31:37.425219+00:00
-- url     : https://prove2.me/theorems/f2da3317-6d41-408a-9c36-a2a74b4cbb46
-- title:
--   LevyStochCalc source proof: LevyStochCalc.BSDEJ.Contraction.sq_generator_sub_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F000

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


theorem _root_.Prove2MeSourceProof.h_99da3ce4a2e20155bfe0bf4c (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    (f s y₁ z₁ u₁ - f s y₂ z₂ u₂) ^ 2
      ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  set A : ℝ≥0∞ := ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hA
  -- Real-valued form of the `ℝ≥0∞` Lipschitz clause, by the technique of
  -- `Existence.abs_sub_le_of_lipschitz` (which is stated for a generator carrying an extra
  -- forward-process argument `x` that this clause has none of; the conversion itself never
  -- uses `x`, so it is reproduced here directly rather than routed through `BSDEJData`).
  have hroot : A ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt A.toReal) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hu]
  have key := hlip s y₁ y₂ z₁ z₂ u₁ u₂
  rw [hroot] at key
  have hne : ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
      + ENNReal.ofReal (Real.sqrt A.toReal)) ≠ ⊤ := by finiteness
  have hmono := ENNReal.toReal_mono hne key
  rw [ENNReal.toReal_mul, ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
    ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hL,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmono
  -- hmono : |f s y₁ z₁ u₁ - f s y₂ z₂ u₂| ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖ + √A.toReal)
  set Δf := f s y₁ z₁ u₁ - f s y₂ z₂ u₂
  set dy := |y₁ - y₂|
  set dz := ‖z₁ - z₂‖
  set r := Real.sqrt A.toReal
  have hΔf_sq : Δf ^ 2 ≤ (L * (dy + dz + r)) ^ 2 := by
    have h0 : 0 ≤ |Δf| := abs_nonneg _
    have hp := pow_le_pow_left₀ h0 hmono 2
    rwa [sq_abs] at hp
  have hthree : (dy + dz + r) ^ 2 ≤ 3 * (dy ^ 2 + dz ^ 2 + r ^ 2) := LevyStochCalc.BSDEJ.Contraction.sq_add_add_le_three dy dz r
  have hLsq : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  have hstep : (L * (dy + dz + r)) ^ 2 ≤ L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hthree hLsq
  have hdy_sq : dy ^ 2 = (y₁ - y₂) ^ 2 := sq_abs _
  have hdz_sq : dz ^ 2 ≤ ∑ j, (z₁ j - z₂ j) ^ 2 := by
    have h := LevyStochCalc.BSDEJ.Contraction.sq_norm_pi_le_sum_sq (z₁ - z₂)
    simpa [Pi.sub_apply] using h
  have hr_sq : r ^ 2 = A.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hmono2 : dy ^ 2 + dz ^ 2 + r ^ 2
      ≤ (y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal := by
    rw [hdy_sq, hr_sq]; linarith [hdz_sq]
  have hfinal : L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2))
      ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal) := by
    nlinarith [mul_le_mul_of_nonneg_left hmono2 hLsq]
  calc Δf ^ 2 ≤ (L * (dy + dz + r)) ^ 2 := hΔf_sq
    _ ≤ L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2)) := hstep
    _ ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal) := hfinal
end LevyStochCalc.BSDEJ.Contraction


