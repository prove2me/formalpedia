-- Prove2me | solution 1 for Auto.cycMb_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:12:35.499635+00:00
-- url     : https://prove2.me/submissions/5193a224-4307-487d-87b7-e11d98cf8538

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_blk3_conjTranspose

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
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
omit [DecidableEq ι] [Fintype ι]
namespace Auto
theorem _root_.solution : (blk3 (cycMb W0 W1 W2)).IsHermitian := by
  rw [Matrix.IsHermitian, cycMb, blk3_conjTranspose]
  simp
end Auto
