-- Prove2me | solution 1 for Auto.aux_ErgodicBox.eLpNorm_two_sq_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:44:08.148419+00:00
-- url     : https://prove2.me/submissions/f21e79ea-c0ba-47f6-8351-3ed7e6fa4281

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [ENorm E] (μ : Measure α) (f : α → E) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num
end Auto.aux_ErgodicBox
