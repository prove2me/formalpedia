-- Prove2me | solution 1 for Auto.costInt_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:17:25.540307+00:00
-- url     : https://prove2.me/submissions/3e20c521-e068-43ba-b515-1196f9c30b59

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_trace_fromBlocks__783b901110bc

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution (A1 A2 K11 K12 K21 K22 X1 X2 : Matrix ι ι ℂ) :
    costInt (Matrix.fromBlocks A1 0 0 A2) (Matrix.fromBlocks K11 K12 K21 K22) (Matrix.fromBlocks
      X1 0 0 X2) = costInt A1 K11 X1 + costInt A2 K22 X2 := by
  classical
  simp only [costInt, hsRe, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    trace_fromBlocks']
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.conjTranspose_zero,
    Complex.add_re]
  ring
end Auto
