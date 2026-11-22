-- Prove2me | solution 1 for Auto.rdiag_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:31:18.938137+00:00
-- url     : https://prove2.me/submissions/08eb217b-a24f-4bf4-8193-5c779a6b1615

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution (f : ι → ℝ) :
    (rdiag f).IsHermitian := by
  simp [rdiag, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
end Auto
