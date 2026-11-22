-- Prove2me | solution 1 for Auto.wGram_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:44:15.340855+00:00
-- url     : https://prove2.me/submissions/914c355c-9e5d-4d7d-ab18-44a487f494e1

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_rdiag_isHermitian

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq κ] [Fintype κ]
namespace Auto
theorem _root_.solution (B : Matrix ι κ ℂ) (f : ι → ℝ) : (wGram B f).IsHermitian := by
  rw [wGram, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (rdiag_isHermitian f).eq, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
end Auto
