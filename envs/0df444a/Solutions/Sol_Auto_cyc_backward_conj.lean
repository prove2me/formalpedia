-- Prove2me | solution 1 for Auto.cyc_backward_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:12:09.087485+00:00
-- url     : https://prove2.me/submissions/ced5bd87-ba6a-41cb-b773-40a91c958b59

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
omit [DecidableEq ι]
namespace Auto
theorem _root_.solution (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) :
    (D0 * W2ᴴ * D2 * W1ᴴ * D1 * W0ᴴ).trace = star ((D0 * W0 * D1 * W1 * D2 * W2).trace) := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, hD0.eq, hD1.eq, hD2.eq, Matrix.mul_assoc]
  have := Matrix.trace_mul_comm D0 (W2ᴴ * (D2 * (W1ᴴ * (D1 * W0ᴴ))))
  simp only [Matrix.mul_assoc] at this
  rw [this]
end Auto
