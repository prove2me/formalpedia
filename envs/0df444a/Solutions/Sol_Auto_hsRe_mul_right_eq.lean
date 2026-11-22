-- Prove2me | solution 1 for Auto.hsRe_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:08:18.917826+00:00
-- url     : https://prove2.me/submissions/3a69449b-062b-45d8-80bd-d75b1c6065ad

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsRe_eq_re_trace

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
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
omit [DecidableEq n]
namespace Auto
theorem _root_.solution (A X : Matrix n n ℂ) :
    hsRe X (X * A) = (((Xᴴ * X) * A).trace).re := by
  rw [hsRe_eq_re_trace, ← Matrix.mul_assoc]
end Auto
