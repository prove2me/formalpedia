-- Prove2me | solution 1 for Auto.blk3_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:48.749879+00:00
-- url     : https://prove2.me/submissions/7dc2dbcb-e269-4ef1-a992-8ff3d6d2217b

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
theorem _root_.solution (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    (blk3 X).trace = (X 0 0).trace + (X 1 1).trace + (X 2 2).trace := by
  simp only [blk3, Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three]
end Auto
