-- Prove2me | solution 1 for Auto.blk3_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:30:58.283585+00:00
-- url     : https://prove2.me/submissions/c12b3db2-9f63-47ca-8ad2-a85bcaee7ceb

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
theorem _root_.solution (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (X * Y) = blk3 X * blk3 Y := (Matrix.compRingEquiv (Fin 3) ι ℂ).map_mul X Y
end Auto
