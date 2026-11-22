-- Prove2me | solution 1 for Auto.hsRe_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:29:42.211777+00:00
-- url     : https://prove2.me/submissions/20fcff7b-daa0-4de3-acfd-fef5ae76557f

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
variable {m n : Type*} [Fintype m] [Fintype n]
namespace Auto
theorem _root_.solution (c : ℝ) (X Y : Matrix m n ℂ) :
    hsRe X (c • Y) = c * hsRe X Y := by
  simp [hsRe, Matrix.mul_smul, Matrix.trace_smul]
end Auto
