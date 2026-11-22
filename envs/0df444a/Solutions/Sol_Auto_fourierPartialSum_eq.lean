-- Prove2me | solution 1 for Auto.fourierPartialSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:54:21.811179+00:00
-- url     : https://prove2.me/submissions/d7ae9f59-33dc-4b07-963b-06a0e6dee3e2

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    Triangular.fourierPartialSum f N x = fourierPartialSum f N x := by
  unfold Triangular.fourierPartialSum fourierPartialSum fourierCoeffOne
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fourierCoeffOn_eq_integral, fourier_coe_apply]
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_one, div_one, one_smul, smul_eq_mul,
    Int.cast_neg]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mul_comm]
  ring_nf
end Auto
