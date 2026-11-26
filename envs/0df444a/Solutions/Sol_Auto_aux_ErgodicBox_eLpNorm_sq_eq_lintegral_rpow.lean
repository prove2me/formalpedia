-- Prove2me | solution 1 for Auto.aux_ErgodicBox.eLpNorm_sq_eq_lintegral_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:52.436331+00:00
-- url     : https://prove2.me/submissions/14f54a72-bb48-4069-a61f-7a92399a7073

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
theorem _root_.solution
    {X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [ENorm E]
    (μ : Measure X) (F : X → E) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm F p μ ^ 2 =
      (∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ) ^ (2 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  have hexp : (1 / p.toReal) * (↑(2 : ℕ) : ℝ) = 2 / p.toReal := by ring
  rw [hexp]
end Auto.aux_ErgodicBox
