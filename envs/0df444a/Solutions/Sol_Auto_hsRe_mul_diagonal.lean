-- Prove2me | solution 1 for Auto.hsRe_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:04:52.393311+00:00
-- url     : https://prove2.me/submissions/45655115-8211-4f12-a62f-4ce34a1b7701

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
    hsRe X (X * diagonal (fun i => (a i : ℂ))) = ∑ i, ∑ j, a j * ‖X i j‖ ^ 2 := by
  rw [hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, mul_comm]
  norm_cast
end Auto
