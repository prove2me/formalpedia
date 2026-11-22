-- Prove2me | solution 1 for Auto.fourierPartialSum_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:53:29.675924+00:00
-- url     : https://prove2.me/submissions/553bc1a4-34a7-4bfd-a97c-502c837940dc

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_fourierCoeffOne_exp
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {k : ℤ} {N : ℕ} (hk : k.natAbs ≤ N) (x : ℝ) :
    fourierPartialSum (fun x => Complex.exp (2 * π * Complex.I * k * x)) N x =
      Complex.exp (2 * π * Complex.I * k * x) := by
  unfold fourierPartialSum
  simp_rw [fourierCoeffOne_exp, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (by simp only [Finset.mem_Icc]; omega)]
end Auto
