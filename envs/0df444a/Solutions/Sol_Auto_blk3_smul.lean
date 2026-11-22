-- Prove2me | solution 1 for Auto.blk3_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:13:31.974489+00:00
-- url     : https://prove2.me/submissions/efafe8b3-8103-492c-bcc7-46066875dde2

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
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
omit [DecidableEq ι] [Fintype ι]
namespace Auto
theorem _root_.solution (c : ℂ) (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (c • X) = c • blk3 X := by
  ext ⟨v, a⟩ ⟨w, b⟩; simp [blk3, Matrix.comp_apply]
end Auto
