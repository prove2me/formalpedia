-- Prove2me | solution 1 for Auto.integrable_re_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:42.620697+00:00
-- url     : https://prove2.me/submissions/ae011260-dddd-4358-9ecb-96ae8754344c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_re_trace_mul_eq_sum

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
theorem _root_.solution {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    Integrable (fun z => ((C * M z).trace).re) ν := by
  simp_rw [re_trace_mul_eq_sum, Complex.re_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hM i j).mul_const _).re
end Auto
