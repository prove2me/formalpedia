-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_two_sq_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:37:49.450943+00:00
-- url     : https://prove2.me/submissions/d35f6ce2-ec05-4f71-80a2-0780ffd48e3e

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
theorem _root_.solution {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [ENorm E] (μ : Measure α) (f : α → E) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num
end Auto.aux_CuboidNorm
