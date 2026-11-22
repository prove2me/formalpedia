-- Prove2me | solution 1 for Auto.integrable_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:25.943916+00:00
-- url     : https://prove2.me/submissions/447f4de4-de21-41de-8e31-7309c82e74ec

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
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
omit [DecidableEq n]
namespace Auto
theorem _root_.solution {M : Z → Matrix n n ℂ} (hM : ∀ i j, Integrable (fun z => M z i j) ν)
    (C : Matrix n n ℂ) :
    Integrable (fun z => ∑ i, ∑ j, M z i j * C i j) ν :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hM i j).mul_const _
end Auto
