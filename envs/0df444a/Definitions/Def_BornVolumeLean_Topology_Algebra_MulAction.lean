-- Prove2me | Definitions.Def_BornVolumeLean_Topology_Algebra_MulAction
-- name    : BornVolumeLean_Topology_Algebra_MulAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:09.314148+00:00
-- url     : https://prove2.me/theorems/1c151e62-d585-4f32-b43b-cb7be769894b
-- title:
--   Mul Action
-- statement:
--   Definitions and structural lemmas for Mul Action, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Topology/Algebra/MulAction.lean

module
public import Mathlib.Topology.Algebra.MulAction
set_option autoImplicit false
@[expose] public section
@[expose] public section
@[to_additive /-- A `SubAddAction` inherits the continuity of the action of each element. -/]
instance SubMulAction.continuousConstSMul_staged {M X : Type*} [TopologicalSpace X] [Monoid M]
    [MulAction M X] [ContinuousConstSMul M X] (p : SubMulAction M X) :
    ContinuousConstSMul M p :=
  ⟨fun c ↦ ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩
instance Units.continuousConstSMul_nonZero_staged {R M : Type*} [TopologicalSpace M] [Monoid R]
    [AddCommMonoid M] [DistribMulAction R M] [ContinuousConstSMul Rˣ M] :
    ContinuousConstSMul Rˣ {x : M // x ≠ 0} :=
  inferInstanceAs (ContinuousConstSMul Rˣ (Units.nonZeroSubMul R M))


