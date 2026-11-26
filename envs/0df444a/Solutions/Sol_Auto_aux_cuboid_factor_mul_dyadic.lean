-- Prove2me | solution 1 for Auto.aux_cuboid_factor_mul_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:47.029184+00:00
-- url     : https://prove2.me/submissions/7630099a-4da8-4adb-9649-9f0a21f368db

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
theorem _root_.solution (n : ℕ) :
    (ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
      ENNReal.ofReal ((1 : ℝ) / 8) ^ n) *
      ((2 : ℝ≥0∞) ^ (3 * n + 6)) = 1 := by
  norm_num [ENNReal.ofReal_div_of_pos]
  have h8 : (8 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 3 := by norm_num
  rw [h8, ENNReal.inv_pow]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  have hexp : 3 * 2 + 3 * n = 3 * n + 6 := by omega
  rw [hexp, ← ENNReal.inv_pow]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
end Auto
