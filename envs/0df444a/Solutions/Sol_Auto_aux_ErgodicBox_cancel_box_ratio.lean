-- Prove2me | solution 1 for Auto.aux_ErgodicBox.cancel_box_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:08.028955+00:00
-- url     : https://prove2.me/submissions/91e93b5e-c7f4-4588-8338-b1d8e1c5324d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_card_box
public import Theorems.Thm_Auto_aux_ErgodicBox_card_box_double

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {n M : ℕ} (hM : 0 < M)
    {E A P : ℝ≥0∞}
    (h : ((box n M).card : ℝ≥0∞) * E ≤
      A * ((box n (M + M)).card : ℝ≥0∞) * P) :
    E ≤ A * ((2 ^ n : ℕ) : ℝ≥0∞) * P := by
  have hcard : ((box n (M + M)).card : ℝ≥0∞) =
      ((2 ^ n : ℕ) : ℝ≥0∞) * ((box n M).card : ℝ≥0∞) := by
    rw [card_box_double]
    norm_cast
  have hb0 : ((box n M).card : ℝ≥0∞) ≠ 0 := by
    rw [card_box]
    apply ENNReal.coe_ne_zero.mpr
    norm_cast
    exact pow_ne_zero _ (Nat.ne_of_gt hM)
  have hbtop : ((box n M).card : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  apply (ENNReal.mul_le_mul_iff_right hb0 hbtop).mp
  calc
    ((box n M).card : ℝ≥0∞) * E ≤
        A * ((box n (M + M)).card : ℝ≥0∞) * P := h
    _ = ((box n M).card : ℝ≥0∞) *
        (A * ((2 ^ n : ℕ) : ℝ≥0∞) * P) := by
      rw [hcard]
      ac_rfl
end Auto.aux_ErgodicBox
