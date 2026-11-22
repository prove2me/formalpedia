-- Prove2me | solution 1 for Auto.re_sum_matIntegral_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:08:53.942806+00:00
-- url     : https://prove2.me/submissions/1e2ef315-6ad9-4f6b-a73c-4791e2f1c3a4

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matIntegral_apply
public import Theorems.Thm_Auto_integrable_sum_mul

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
    (∑ i, ∑ j, matIntegral ν M i j * C i j).re = ∫ z, (∑ i, ∑ j, M z i j * C i j).re ∂ν := by
  have h := integral_re (integrable_sum_mul hM C)
  simp only [RCLike.re_to_complex] at h
  simp only [matIntegral_apply]
  rw [h]
  congr 1
  symm
  calc ∫ z, ∑ i, ∑ j, M z i j * C i j ∂ν = ∑ i, ∫ z, ∑ j, M z i j * C i j ∂ν :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).mul_const _
    _ = ∑ i, ∑ j, ∫ z, M z i j * C i j ∂ν :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => (hM i j).mul_const _
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        integral_mul_const _ _
end Auto
