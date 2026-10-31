-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P94
-- name    : QAlgorithms_Papers_Independent_Intake100_P94
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:45:09.977993+00:00
-- url     : https://prove2.me/theorems/eba5ced8-e68f-471e-9bcf-1b9968683a2c
-- title:
--   Definitions for Differentiable mappings between spaces of sections
-- statement:
--   The objects the formalized statements of *Differentiable mappings between spaces of sections* (arXiv:1308.1172) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MBOrder`: Sections 1.1--1.2, PDF pp. 3--4: Michal--Bastiani C^r on an open subset, for r in the nonnegative integers together with infinity. Complex spaces are differentiated over their underlying real spaces. Finite orders impose only the indicated finite directional derivatives; infinity imposes every finite order. The source states the equivalence with its recursively doubled full differential definition in Section 1.1.
--   - `CrAtlas`: Section 1.2, PDF p. 4: a C^r atlas on a Hausdorff space modelled on a locally convex real space. Both orders of chart pairs are tested. The ambient locally convex and Hausdorff assumptions are explicit in LCVectorBundle and in every theorem using this atlas.
--   - `LCVectorBundle`: Definitions 3.1 and Remark 3.2, PDF p. 9: a locally convex C^r vector bundle, presented by a topological bundle's linear trivialization atlas and the joint C^r transition evaluations in base charts. These charts specify the total-space C^r structure by their product charts. Only the fibre coordinate of a transition needs testing, since its base coordinate is the identity. No regularity of the map into an operator space is imposed. The real model Z also covers underlying real charts of complex manifolds. All fibre topologies are induced by the total space through the generic FiberBundle structure.
--   - `WhitneyTotal`: Section 3.11, PDF p. 11: the actual topological total space of the Whitney sum. A point consists of two vectors over the same base point. It has the subspace topology from the product of the two total spaces; local trivializations identify it with U times the product fibre.
--   - `OpenWhitneyDomain`: Section 3.13, PDF p. 12: U plus E2 is the subset of the actual Whitney sum whose first vector belongs to U. This is the displayed fibrewise union, expressed without a choice of a base point.
-- source:
--   Differentiable mappings between spaces of sections, arXiv:1308.1172v1, https://arxiv.org/abs/1308.1172v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

/-!
Statements from Helge Gloeckner, arXiv:1308.1172v1.
The finite-order directional calculus is reused from the pinned accepted library.
The source explicitly identifies this calculus with its full recursive calculus
(Section 1.1, PDF pp. 3--4). No recursive differential identity is asserted here.
The bundle atlas below requires joint regularity of transition evaluation, with
no norm on the typical fibre and no operator-valued regularity assumption.
Deferred nodes and exact missing constructions are recorded in this unit's
HARD.md and GAPS.json. Compilation and independent moderation are pending.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P94

open Set Filter Topology Bundle
open QAlgorithms.Papers.Independent.Gap48.P05

universe u v w z

/-- Sections 1.1--1.2, PDF pp. 3--4: Michal--Bastiani C^r on an open
subset, for r in the nonnegative integers together with infinity.
Complex spaces are differentiated over their underlying real spaces.
Finite orders impose only the indicated finite directional derivatives;
infinity imposes every finite order. The source states the equivalence
with its recursively doubled full differential definition in Section 1.1. -/
def MBOrder {E : Type u} {F : Type v}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (r : WithTop ℕ) (U : Set E) (f : E → F) : Prop :=
  ∀ n : ℕ, (n : WithTop ℕ) ≤ r → BastianiCkOn n U f

/-- Sanity: the constant zero map has every order of regularity, including
order zero, on the empty open set and on the whole space alike. -/
example {E : Type u} {F : Type v}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (r : WithTop ℕ) (U : Set E) : MBOrder r U (fun _ => (0 : F)) := by
  intro n hn
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro j hj
    exact continuousOn_const
  · intro j hj x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

/-- Section 1.2, PDF p. 4: a C^r atlas on a Hausdorff space modelled
on a locally convex real space. Both orders of chart pairs are tested.
The ambient locally convex and Hausdorff assumptions are explicit in
LCVectorBundle and in every theorem using this atlas. -/
def CrAtlas (r : WithTop ℕ) (Z : Type u) (X : Type v)
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace X] [ChartedSpace Z X] : Prop :=
  ∀ c ∈ atlas Z X, ∀ d ∈ atlas Z X,
    MBOrder r (c.symm.trans d).source (c.symm.trans d)

/-- Definitions 3.1 and Remark 3.2, PDF p. 9: a locally convex C^r
vector bundle, presented by a topological bundle's linear trivialization
atlas and the joint C^r transition evaluations in base charts. These
charts specify the total-space C^r structure by their product charts.
Only the fibre coordinate of a transition needs testing, since its base
coordinate is the identity. No regularity of the map into an operator
space is imposed. The real model Z also covers underlying real charts
of complex manifolds. All fibre topologies are induced by the total
space through the generic FiberBundle structure. -/
structure LCVectorBundle (r : WithTop ℕ)
    (K : Type u) [RCLike K]
    (Z : Type v) [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
    [LocallyConvexSpace ℝ Z] [T2Space Z]
    (X : Type w) [TopologicalSpace X] [T2Space X] [ChartedSpace Z X]
    (F : Type z) [TopologicalSpace F] [AddCommGroup F]
    [Module K F] [Module ℝ F] [IsScalarTower ℝ K F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
    [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [T2Space (TotalSpace F V)]
    [FiberBundle F V] : Prop where
  baseCr : CrAtlas r Z X
  linear : ∀ e ∈ trivializationAtlas F V, e.IsLinear K
  transitionCr : ∀ e ∈ trivializationAtlas F V,
    ∀ d ∈ trivializationAtlas F V, ∀ c ∈ atlas Z X,
      MBOrder r
        ((c.target ∩ c.symm ⁻¹' (e.baseSet ∩ d.baseSet)) ×ˢ
          (Set.univ : Set F))
        (fun p : Z × F =>
          (d (e.toOpenPartialHomeomorph.symm (c.symm p.1, p.2))).2)

/-- Section 3.11, PDF p. 11: the actual topological total space of the
Whitney sum. A point consists of two vectors over the same base point.
It has the subspace topology from the product of the two total spaces;
local trivializations identify it with U times the product fibre. -/
def WhitneyTotal {X : Type u} (F1 : Type v) (F2 : Type w)
    (V1 : X → Type*) (V2 : X → Type*) :=
  {p : TotalSpace F1 V1 × TotalSpace F2 V2 // p.1.proj = p.2.proj}

/-- The Whitney total space has exactly the product-subspace topology,
with no topology chosen independently of its two input bundles. -/
instance whitneyTotalTopology {X : Type u} {F1 : Type v} {F2 : Type w}
    {V1 : X → Type*} {V2 : X → Type*}
    [TopologicalSpace (TotalSpace F1 V1)]
    [TopologicalSpace (TotalSpace F2 V2)] :
    TopologicalSpace (WhitneyTotal F1 F2 V1 V2) :=
  inferInstanceAs (TopologicalSpace
    {p : TotalSpace F1 V1 × TotalSpace F2 V2 // p.1.proj = p.2.proj})

/-- Section 3.13, PDF p. 12: U plus E2 is the subset of the actual
Whitney sum whose first vector belongs to U. This is the displayed
fibrewise union, expressed without a choice of a base point. -/
def OpenWhitneyDomain {X : Type u} {F1 : Type v} {F2 : Type w}
    {V1 : X → Type*} {V2 : X → Type*}
    (U : Set (TotalSpace F1 V1)) : Set (WhitneyTotal F1 F2 V1 V2) :=
  {p | p.val.1 ∈ U}

/-- Sanity: the empty fibrewise domain is empty, even when the base
or one of the fibres is empty. -/
example {X : Type u} {F1 : Type v} {F2 : Type w}
    {V1 : X → Type*} {V2 : X → Type*} :
    OpenWhitneyDomain (F2 := F2) (V2 := V2)
      (∅ : Set (TotalSpace F1 V1)) = ∅ := rfl

/-- Sanity: an unrestricted first factor gives the whole Whitney sum,
including all allowed zero-dimensional and empty-base cases. -/
example {X : Type u} {F1 : Type v} {F2 : Type w}
    {V1 : X → Type*} {V2 : X → Type*} :
    OpenWhitneyDomain (F2 := F2) (V2 := V2)
      (Set.univ : Set (TotalSpace F1 V1)) = Set.univ := rfl

section BundleResults

variable {K : Type u} [RCLike K]
variable {Z : Type v} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
variable [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
variable [LocallyConvexSpace ℝ Z] [T2Space Z]
variable {X : Type w} [TopologicalSpace X] [T2Space X] [ChartedSpace Z X]
variable {F : Type z} [TopologicalSpace F] [AddCommGroup F]
variable [Module K F] [Module ℝ F] [IsScalarTower ℝ K F]
variable [IsTopologicalAddGroup F] [ContinuousSMul K F] [ContinuousSMul ℝ F]
variable [LocallyConvexSpace ℝ F] [T2Space F]
variable {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
variable [∀ x, TopologicalSpace (V x)]
variable [TopologicalSpace (TotalSpace F V)] [T2Space (TotalSpace F V)]
variable [FiberBundle F V]

/-- Sanity: the chosen atlas supplies a genuine local trivialization at
each base point, and its fibre maps are linear. This also checks that
no countability or connectedness condition is part of the bundle object. -/
example (r : WithTop ℕ) (B : LCVectorBundle r K Z X F V) (x : X) :
    ∃ e ∈ trivializationAtlas F V, x ∈ e.baseSet ∧ e.IsLinear K := by
  refine ⟨trivializationAt F V x, trivialization_mem_atlas F V x, ?_⟩
  exact ⟨mem_baseSet_trivializationAt F V x,
    B.linear _ (trivialization_mem_atlas F V x)⟩

variable {F2 : Type*} [TopologicalSpace F2] [AddCommGroup F2]
variable [Module K F2] [Module ℝ F2] [IsScalarTower ℝ K F2]
variable [IsTopologicalAddGroup F2] [ContinuousSMul K F2] [ContinuousSMul ℝ F2]
variable [LocallyConvexSpace ℝ F2] [T2Space F2]
variable {V2 : X → Type*} [∀ x, AddCommGroup (V2 x)] [∀ x, Module K (V2 x)]
variable [∀ x, TopologicalSpace (V2 x)]
variable [TopologicalSpace (TotalSpace F2 V2)] [T2Space (TotalSpace F2 V2)]
variable [FiberBundle F2 V2]

end BundleResults

end QAlgorithms.Papers.Independent.Intake100.P94


