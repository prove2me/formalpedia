-- Prove2me | solution 1 for Auto.hsRe_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:40.690131+00:00
-- url     : https://prove2.me/submissions/d06d60c6-707e-4471-9e86-2fb810ebaa6e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution (a : n → ℝ) (X : Matrix n n ℂ) :
    hsRe X (diagonal (fun i => (a i : ℂ)) * X) = ∑ i, ∑ j, a i * ‖X i j‖ ^ 2 := by
  rw [hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, mul_left_comm, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  norm_cast
end Auto
