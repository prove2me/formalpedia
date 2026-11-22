-- Prove2me | solution 1 for Auto.rowMat_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:43:17.391309+00:00
-- url     : https://prove2.me/submissions/d4835296-1058-4aa4-a833-9ac5e149830a

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
theorem _root_.solution (W V : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * rowMat W V = Matrix.fromBlocks (Wᴴ * W) (Wᴴ * Vᴴ) (V * W) (V * Vᴴ) := by
  simp [rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose]
end Auto
