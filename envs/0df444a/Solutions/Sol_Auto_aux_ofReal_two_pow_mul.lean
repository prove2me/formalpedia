-- Prove2me | solution 1 for Auto.aux_ofReal_two_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:44.8371+00:00
-- url     : https://prove2.me/submissions/1400d3e9-eeaa-4ebb-bcd5-7fdbf3e11236

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution (n : ℕ) (C : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ n * C) =
      ((2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal C := by
  rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) _)]
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num
end Auto
