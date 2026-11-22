-- Prove2me | solution 1 for Auto.cycDb_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:26.197945+00:00
-- url     : https://prove2.me/submissions/a17b0492-1f5a-438e-ac8a-724cb49593f7

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
theorem _root_.solution (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (blk3 (cycDb D0 D1 D2)).IsHermitian := by
  rw [Matrix.IsHermitian, cycDb, blk3_conjTranspose]
  simp [hD0.eq, hD1.eq, hD2.eq]
end Auto
