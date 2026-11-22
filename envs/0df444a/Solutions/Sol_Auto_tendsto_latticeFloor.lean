-- Prove2me | solution 1 for Auto.tendsto_latticeFloor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:35.715559+00:00
-- url     : https://prove2.me/submissions/e4754b82-7823-4ff2-9406-fe38ed2c08ba

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_sub_latticeFloor_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Auto
theorem _root_.solution (x : Fin d → ℝ) :
    Tendsto (fun N : ℕ => latticeFloor N x) atTop (𝓝 x) := by
  rw [tendsto_pi_nhds]
  intro i
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have : Tendsto (fun N : ℕ => x i - latticeFloor N x i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact abs_sub_latticeFloor_le hN x i
  have := (tendsto_const_nhds (x := x i)).sub this
  simpa using this
end Auto
