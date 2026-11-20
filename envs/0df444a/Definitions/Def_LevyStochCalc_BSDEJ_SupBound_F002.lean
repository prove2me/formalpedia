-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F002
-- name    : LevyStochCalc_BSDEJ_SupBound_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:14:44.593438+00:00
-- url     : https://prove2.me/theorems/f672272c-1cdf-4672-9a88-150d1b0aca5a
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.SupBound
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.SupBound. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F001
import Definitions.Def_SourceProof_d4d30e0975338aead626e008

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

/-- The `S²` seminorm of a time integral is at most `T` times the `L²` norm of its integrand. -/
theorem lintegral_biSup_sq_setIntegral_le (g : Ω → ℝ → ℝ) (T : ℝ)
    (hg : ∀ ω, IntegrableOn (g ω) (Set.Icc (0 : ℝ) T)) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ENNReal.ofReal T
        * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  have key : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    (biSup_sq_setIntegral_le g T ω).trans
      (_root_.Prove2MeSourceProof.h_d4d30e0975338aead626e008 T (hg ω).aestronglyMeasurable.enorm)
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal T
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_mono key
    _ = ENNReal.ofReal T
          * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-! ### Scalar multiples -/

/-- The squared supremum over `[0, T]` of a scalar multiple of a process is the squared norm of
the scalar times the squared supremum of the process. -/
theorem biSup_sq_const_mul (c : ℝ) (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c * M t ω‖₊ : ℝ≥0∞) ^ 2
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 := by
  simp only [nnnorm_mul, ENNReal.coe_mul, mul_pow, ENNReal.mul_iSup]
/-- The `S²` seminorm of a scalar multiple of a process is the squared norm of the scalar times
the `S²` seminorm of the process. -/
theorem lintegral_biSup_sq_const_mul (c : ℝ) (M : ℝ → Ω → ℝ) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c * M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      = (‖c‖₊ : ℝ≥0∞) ^ 2
        * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  exact lintegral_congr fun ω => biSup_sq_const_mul c M T ω
end LevyStochCalc.BSDEJ.SupBound


