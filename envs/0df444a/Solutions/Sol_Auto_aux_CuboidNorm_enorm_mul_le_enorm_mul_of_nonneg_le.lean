-- Prove2me | solution 1 for Auto.aux_CuboidNorm.enorm_mul_le_enorm_mul_of_nonneg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:37.021124+00:00
-- url     : https://prove2.me/submissions/e3089a2b-cc12-4a08-b2b0-3bc62287134f

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {c w h : ℝ}
    (hc : 0 ≤ c) (hcw : c ≤ w) :
    ‖c * h‖ₑ ≤ ‖w * h‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_mul, abs_mul, abs_of_nonneg hc,
    abs_of_nonneg (le_trans hc hcw)]
  exact mul_le_mul_of_nonneg_right hcw (abs_nonneg h)
end Auto.aux_CuboidNorm
