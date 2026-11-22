-- Prove2me | solution 1 for Auto.norm_carlesonMoll_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:51.851872+00:00
-- url     : https://prove2.me/submissions/dba7c2f7-73d2-4515-b53d-2a101e96dcde

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Auto
theorem _root_.solution (k : ℕ) {h : ℝ → E} {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (x : ℝ) :
    ‖carlesonMoll k h x‖ ≤ B := by
  set φ := (carlesonMollifier k).normed volume
  rw [carlesonMoll, convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ t) (h (x - t))‖ ≤ ∫ t, φ t * B := by
        refine norm_integral_le_of_norm_le ((carlesonMollifier k).integrable_normed.mul_const B)
          (ae_of_all _ fun t => ?_)
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ((carlesonMollifier k).nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hB _) ((carlesonMollifier k).nonneg_normed t)
    _ = B := by rw [integral_mul_const, (carlesonMollifier k).integral_normed, one_mul]
end Auto
