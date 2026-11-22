-- Prove2me | solution 1 for Auto.re_trace_mul_matIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:10:23.515348+00:00
-- url     : https://prove2.me/submissions/570900ec-80bd-4eda-bc3d-3d7645fb072c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_re_sum_matIntegral_mul
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
    ((C * matIntegral ν M).trace).re = ∫ z, ((C * M z).trace).re ∂ν := by
  rw [re_trace_mul_eq_sum]
  have := re_sum_matIntegral_mul hM Cᵀ
  simp only [Matrix.transpose_apply] at this
  rw [this]
  congr 1; funext z
  rw [re_trace_mul_eq_sum]
end Auto
