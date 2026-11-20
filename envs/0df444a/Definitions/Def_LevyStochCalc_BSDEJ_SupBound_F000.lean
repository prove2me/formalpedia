-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
-- name    : LevyStochCalc_BSDEJ_SupBound_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T14:58:21.076751+00:00
-- url     : https://prove2.me/theorems/c87d1ff6-9097-4c3f-b905-39dee70e3026
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

/-- Squaring commutes with suprema in `ℝ≥0∞`. -/
theorem iSup_sq {ι : Sort*} (f : ι → ℝ≥0∞) : (⨆ i, f i) ^ 2 = ⨆ i, f i ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun i => pow_le_pow_left' (le_iSup f i) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  rcases le_total (f i) (f j) with h | h
  · calc f i * f j ≤ f j * f j := mul_le_mul' h le_rfl
      _ = f j ^ 2 := (pow_two (f j)).symm
      _ ≤ ⨆ k, f k ^ 2 := le_iSup (fun k => f k ^ 2) j
  · calc f i * f j ≤ f i * f i := mul_le_mul' le_rfl h
      _ = f i ^ 2 := (pow_two (f i)).symm
      _ ≤ ⨆ k, f k ^ 2 := le_iSup (fun k => f k ^ 2) i
/-- The supremum over `[0, T]` of a square is the square of the supremum over the subtype
`↥(Set.Icc 0 T)`. -/
theorem biSup_sq_eq_iSup_subtype_sq (g : ℝ → ℝ≥0∞) (T : ℝ) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, g t ^ 2 = (⨆ t : Set.Icc (0 : ℝ) T, g (t : ℝ)) ^ 2 := by
  rw [iSup_subtype'' (Set.Icc (0 : ℝ) T) g, iSup_sq]
  exact iSup_congr fun t => (iSup_sq _).symm
/-! ### Doob's `L²` maximal inequality in the `S²` shape -/

/-- **Doob's `L²` maximal inequality**, with the supremum over `[0, T]` inside the square: for a
right-continuous martingale it is at most four times the second moment of the terminal value. -/
theorem lintegral_biSup_sq_le_of_martingale [IsFiniteMeasure μ] {M : ℝ → Ω → ℝ} {T : ℝ}
    {ℱ : Filtration ℝ mΩ} (hM : Martingale M ℱ μ) (hT : 0 ≤ T)
    (hcad : ∀ᵐ ω ∂μ, ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hcongr : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ :=
    lintegral_congr fun ω => biSup_sq_eq_iSup_subtype_sq (fun t => (‖M t ω‖₊ : ℝ≥0∞)) T
  rw [hcongr]
  exact LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale hM hT hcad
/-! ### Subadditivity of the `S²` seminorm -/

/-- The square of a sum of two reals is at most twice the sum of the squares, in `ℝ≥0∞`. -/
theorem sq_enorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
    refine (pow_le_pow_left' (nnnorm_add_le a b) 2).trans ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ((‖a + b‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring
/-- The squared supremum over `[0, T]` of a sum of two processes is at most twice the sum of the
squared suprema. -/
theorem biSup_sq_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2)
        + 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2 := by
  refine iSup₂_le fun t ht => (sq_enorm_add_le (A t ω) (B t ω)).trans (add_le_add ?_ ?_)
  · exact mul_le_mul' le_rfl
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖A t ω‖₊ : ℝ≥0∞) ^ 2) t ht)
  · exact mul_le_mul' le_rfl
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖B t ω‖₊ : ℝ≥0∞) ^ 2) t ht)
/-- The `S²` seminorm of a sum of two processes is at most twice the sum of the `S²` seminorms. -/
theorem lintegral_biSup_sq_add_le (A B : ℝ → Ω → ℝ) (T : ℝ)
    (hB : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) μ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
        + 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ∫⁻ ω, (2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2)
          + 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_mono fun ω => biSup_sq_add_le A B T ω
    _ = ∫⁻ ω, 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
          + ∫⁻ ω, 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_add_right' _ (hB.const_mul 2)
    _ = 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
          + 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
/-- On a finite measure a constant process has finite `S²` seminorm. -/
theorem lintegral_biSup_sq_const_lt_top [IsFiniteMeasure μ] (c : ℝ) (T : ℝ) :
    ∫⁻ _ω, (⨆ _t ∈ Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_le fun _ _ =>
    le_refl ((‖c‖₊ : ℝ≥0∞) ^ 2)) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) (measure_lt_top μ Set.univ)
/-! ### The drift term -/

/-! ### Scalar multiples -/

end LevyStochCalc.BSDEJ.SupBound


