-- Prove2me | solution 1 for Auto.matCost_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:30.677766+00:00
-- url     : https://prove2.me/submissions/3eec21cd-8958-4084-92e4-4da8f0ba21d1

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_comparison

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
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) (hPQ : P ≤ Q) (K : Matrix n n ℂ) :
    matCost Q K ≤ matCost P K := by
  have := matCost_comparison hQ one_pos (by simpa using hPQ) K
  simpa using this
end Auto
