-- Prove2me | solution 1 for Auto.dirichletKernel_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:17.913678+00:00
-- url     : https://prove2.me/submissions/76d7b311-b156-46b6-9525-34c7435a7b7c

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
open Real
namespace Auto
theorem _root_.solution (N : ℕ) : Function.Periodic (dirichletKernel N) 1 := by
  intro s
  unfold dirichletKernel
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (2 * π * Complex.I * n * ((s + 1 : ℝ) : ℂ)) =
      2 * π * Complex.I * n * s + n * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Auto
