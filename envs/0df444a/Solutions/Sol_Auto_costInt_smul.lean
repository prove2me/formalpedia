-- Prove2me | solution 1 for Auto.costInt_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:09:05.162717+00:00
-- url     : https://prove2.me/submissions/b901fd40-d442-4b01-a35a-6a2a2c7378c3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_smul_right

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
omit [DecidableEq n]
namespace Auto
theorem _root_.solution (A K X : Matrix n n ℂ) (c : ℝ) :
    costInt A (c • K) (c • X) = c ^ 2 * costInt A K X := by
  have hc : ∀ (X Y : Matrix n n ℂ), hsRe (c • X) Y = c * hsRe X Y := by
    intro X Y; rw [hsRe_comm, hsRe_smul_right, hsRe_comm]
  unfold costInt
  simp only [Matrix.mul_smul, Matrix.smul_mul, hsRe_smul_right, hc]
  ring
end Auto
