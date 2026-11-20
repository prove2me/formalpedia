-- Prove2me | Definitions.Def_SourceProof_d4d30e0975338aead626e008
-- name    : SourceProof_d4d30e0975338aead626e008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:14:22.940109+00:00
-- url     : https://prove2.me/theorems/40fede31-7d0d-40f8-afe0-303f2151f02a
-- title:
--   LevyStochCalc source module: SourceProof_d4d30e0975338aead626e008
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.SupBound.sq_lintegral_le_ofReal_mul_lintegral_sq` comes from the `LevyStochCalc.BSDEJ.SupBound` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` norm of a sum of a constant, two martingales and a drift

The solution space `S²` of a backward equation asks for
`∫⁻ ω, ⨆ t ∈ [0, T], ‖Y t ω‖ₑ² ∂μ < ⊤`, a supremum over the window taken *inside* the square,
while Doob's `L²` maximal inequality
(`LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale`) is stated with the square
outside a supremum over the subtype `↥(Set.Icc 0 T)`. The two shapes agree, because squaring
commutes with suprema in `ℝ≥0∞`, and the resulting bound is stable under the decomposition
`Y = c + M₁ + M₂ + A` of a Picard iterate into a constant, two stochastic integrals and a
time integral of the generator.

## Main statements

* `biSup_sq_eq_iSup_subtype_sq` — the two shapes of the squared supremum over `[0, T]` agree.
* `lintegral_biSup_sq_le_of_martingale` — Doob's `L²` maximal inequality in the `S²` shape.
* `lintegral_biSup_sq_add_le` — the `S²` seminorm is subadditive up to a factor `2`.
* `lintegral_biSup_sq_const_add_add_add_lt_top` — a sum of a constant and three processes of
  finite `S²` seminorm has finite `S²` seminorm.
* `lintegral_biSup_sq_setIntegral_le` — the `S²` seminorm of a time integral, by Cauchy–Schwarz.
* `lintegral_biSup_sq_const_mul` — the `S²` seminorm of a scalar multiple of a process.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.SupBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Squares and suprema in `ℝ≥0∞` -/

/-! ### Doob's `L²` maximal inequality in the `S²` shape -/

/-! ### Subadditivity of the `S²` seminorm -/

/-! ### The drift term -/


theorem _root_.Prove2MeSourceProof.h_d4d30e0975338aead626e008 (T : ℝ) {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Set.Icc (0 : ℝ) T))) :
    (∫⁻ s in Set.Icc (0 : ℝ) T, f s) ^ 2
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2 := by
  have hsqr : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have hhalf : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have huniv : (volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ = ENNReal.ofReal T := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) T))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, huniv, hsqr, one_pow, one_mul] at h
  calc (∫⁻ s in Set.Icc (0 : ℝ) T, f s) ^ 2
      ≤ ((∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2) ^ ((1 : ℝ) / 2)
          * ENNReal.ofReal T ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' h 2
    _ = ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2 := by
        rw [mul_pow, hhalf, hhalf, mul_comm]
/-! ### Scalar multiples -/

end LevyStochCalc.BSDEJ.SupBound


