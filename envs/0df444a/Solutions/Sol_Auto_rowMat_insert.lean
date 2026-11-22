-- Prove2me | solution 1 for Auto.rowMat_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:43:10.435488+00:00
-- url     : https://prove2.me/submissions/a32f0482-88af-4905-9369-009b842eac1c

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution (W V D : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * D * rowMat W V = Matrix.fromBlocks (Wᴴ * D * W) (Wᴴ * D * Vᴴ) (V * D * W) (V
      * D * Vᴴ) := by
  simp [rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.mul_assoc]
end Auto
