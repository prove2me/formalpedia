-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F001
-- name    : LevyStochCalc_BSDEJ_SupBound_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T14:59:07.967368+00:00
-- url     : https://prove2.me/theorems/5efd46df-7dc7-46a7-a19e-f4bb2d47e802
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.SupBound
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.SupBound. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The squared supremum over `[0, T]` of a time integral is at most the square of the total
integral of the norm of the integrand. -/
theorem biSup_sq_setIntegral_le (g : Ω → ℝ → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞)) ^ 2 := by
  refine iSup₂_le fun t ht => pow_le_pow_left' ?_ 2
  calc (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (‖g ω s‖₊ : ℝ≥0∞) :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) :=
        lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)
/-! ### Scalar multiples -/

end LevyStochCalc.BSDEJ.SupBound


