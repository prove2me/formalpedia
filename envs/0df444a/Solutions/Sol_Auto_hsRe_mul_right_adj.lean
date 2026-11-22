-- Prove2me | solution 1 for Auto.hsRe_mul_right_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:58.869326+00:00
-- url     : https://prove2.me/submissions/83d39881-b803-4c25-9525-81c7150e693c

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    hsRe X (Y * A) = hsRe (X * A) Y := by
  simp only [hsRe, Matrix.conjTranspose_mul, hA.eq]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
end Auto
