-- Prove2me | Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
-- name    : MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T00:26:19.973879+00:00
-- url     : https://prove2.me/theorems/b1f8670c-7a49-49c9-86ae-bc9a9e45ccbc
-- title:
--   Restriction maps on the original continuous first-cohomology presentation
-- statement:
--   Let G be a group with a topology, M an abelian topological group, and G act on M by automorphisms. For every subgroup S with its induced topology, restriction of continuous cocycles induces a homomorphism $$H^1_{\mathrm{cont}}(G,M)\longrightarrow H^1_{\mathrm{cont}}(S,M).$$ Retain the original restricted cocycle, continuous-cocycle homomorphism, intermediate class map and quotient homomorphism, with their immediate kernel and class-map laws. All six complete original types and four constructor values are compared. Named downstream consumers are actual norm subgroup restrictions and local Selmer conditions. No continuity of multiplication on G, continuity of the action, or closedness of S is added.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologySubgroupRestriction constructor declarations and immediate quotient laws, Apache-2.0. Original complete types and constructor values compared; no extra owned theorem credit for structural laws.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of continuous cocycles descends to continuous
H1 for every subgroup with its induced topology. A restricted class is
zero precisely when the restricted cocycle is a subgroup coboundary.
Named downstream consumer: local conditions on actual norm Kummer classes.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData

noncomputable section
namespace MazurTransfer.ContinuousFirstCohomologySubgroupRestriction
open ContinuousFirstCohomologyPresentation
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
variable (S : Subgroup G)

def restrictCocycle (z : groupCohomology.cocycles₁ (rep G M)) :
    groupCohomology.cocycles₁ (rep S M) :=
  ⟨fun s => z s.val, (groupCohomology.mem_cocycles₁_iff _).mpr
    (fun s t => (groupCohomology.mem_cocycles₁_iff _).mp z.property s.val t.val)⟩

def restrictContinuousCocycles : continuousCocycles G M →+ continuousCocycles S M where
  toFun z := ⟨restrictCocycle G M S z.val, z.property.comp continuous_subtype_val⟩
  map_zero' := by apply Subtype.ext; apply groupCohomology.cocycles₁_ext; intro s; rfl
  map_add' z w := by apply Subtype.ext; apply groupCohomology.cocycles₁_ext; intro s; rfl

def restrictedClass : continuousCocycles G M →+ H1 S M :=
  (classMap S M).comp (restrictContinuousCocycles G M S)

theorem restrictedClass_kernel : (forgetCocycles G M).ker ≤ (restrictedClass G M S).ker := by
  intro z hz
  change restrictedClass G M S z = 0
  apply (classMap_eq_zero_iff S M _).mpr
  have hz' : (z.val : G → Additive M) ∈ groupCohomology.coboundaries₁ (rep G M) :=
    (forgetCocycles_eq_zero_iff G M z).mp hz
  obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => (Additive.toMul (z.val g) : M)) hz'
  have h : groupCohomology.IsMulCoboundary₁
      (fun s : S => (Additive.toMul (z.val s.val) : M)) := ⟨m, fun s => hm s.val⟩
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁ h).property

def restriction : H1 G M →+ H1 S M :=
  QuotientAddGroup.lift (forgetCocycles G M).ker (restrictedClass G M S)
    (restrictedClass_kernel G M S)

@[simp] theorem restriction_classMap (z : continuousCocycles G M) :
    restriction G M S (classMap G M z) = classMap S M (restrictContinuousCocycles G M S z) := rfl


end MazurTransfer.ContinuousFirstCohomologySubgroupRestriction
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restrictCocycle
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restrictContinuousCocycles
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restrictedClass
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restrictedClass_kernel
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restriction
#print axioms MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restriction_classMap


