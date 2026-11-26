-- Prove2me | solution 1 for Auto.aux_half_mul_half_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:25.9358+00:00
-- url     : https://prove2.me/submissions/7dfca472-2872-4cb9-a12e-48d6fc0a89bd

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution (C E : ℝ≥0∞) :
    (C ^ ((2 : ℝ)⁻¹) * E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = C * E := by
  rw [ENNReal.rpow_two, mul_pow]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num
end Auto
