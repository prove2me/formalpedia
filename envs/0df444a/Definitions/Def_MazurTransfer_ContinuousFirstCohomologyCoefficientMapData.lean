-- Prove2me | Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
-- name    : MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T00:27:16.407895+00:00
-- url     : https://prove2.me/theorems/6cd79f89-a937-40b0-8226-d24acf6e7960
-- title:
--   Continuous equivariant coefficient maps on the original continuous H1 presentation
-- statement:
--   Let G be a group with a topology acting by automorphisms on abelian topological groups M and N. A continuous equivariant group homomorphism f from M to N induces $$H^1_{\mathrm{cont}}(G,M)\longrightarrow H^1_{\mathrm{cont}}(G,N).$$ Retain the original cocycle, continuous-cocycle, intermediate class and quotient constructors, plus the immediate kernel and class-map laws. All six complete original types and four constructor values are compared. Named downstream consumers are restriction compatibility and the actual arithmetic norm-character Kummer images in local Selmer conditions. The induced topologies and original group/action hypotheses remain unchanged.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyCoefficientMap constructor declarations and immediate quotient laws, Apache-2.0. Original complete types and constructor values compared; no extra owned theorem credit for structural laws.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous equivariant coefficient homomorphisms induce
maps on the EXISTING continuous-cocycle H1 presentation and commute with
restriction to every subgroup. Named downstream consumer: the actual
arithmetic norm-character Kummer images and local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData

noncomputable section
namespace MazurTransfer.ContinuousFirstCohomologyCoefficientMap
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
variable (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalGroup M] [IsTopologicalGroup N]
variable (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
  (hc : Continuous f)

def mapCocycle (z : groupCohomology.cocycles₁ (rep G M)) :
    groupCohomology.cocycles₁ (rep G N) :=
  groupCohomology.cocyclesOfIsMulCocycle₁ (f := fun g => f (Additive.toMul (z g) : M)) (by
    intro g h
    have hz : (Additive.toMul (z (g * h)) : M) =
        g • (Additive.toMul (z h) : M) * (Additive.toMul (z g) : M) :=
      groupCohomology.isMulCocycle₁_of_mem_cocycles₁
        (fun g : G => (Additive.toMul (z g) : M)) z.property g h
    change f (Additive.toMul (z (g * h)) : M) =
      g • f (Additive.toMul (z h) : M) * f (Additive.toMul (z g) : M)
    rw [hz, map_mul, hf])

def mapContinuousCocycles : continuousCocycles G M →+ continuousCocycles G N where
  toFun z := ⟨mapCocycle G M N f hf z.val, hc.comp z.property⟩
  map_zero' := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Additive.toMul.injective
    change f 1 = 1
    exact map_one f
  map_add' z w := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Additive.toMul.injective
    change f ((Additive.toMul (z.val g) : M) * (Additive.toMul (w.val g) : M)) =
      f (Additive.toMul (z.val g) : M) * f (Additive.toMul (w.val g) : M)
    exact map_mul f _ _

def mappedClass : continuousCocycles G M →+ H1 G N :=
  (classMap G N).comp (mapContinuousCocycles G M N f hf hc)

theorem mappedClass_kernel : (forgetCocycles G M).ker ≤ (mappedClass G M N f hf hc).ker := by
  intro z hz
  change classMap G N (mapContinuousCocycles G M N f hf hc z) = 0
  apply (classMap_eq_zero_iff G N _).mpr
  have hz' := (forgetCocycles_eq_zero_iff G M z).mp hz
  obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => (Additive.toMul (z.val g) : M)) hz'
  have h : groupCohomology.IsMulCoboundary₁ (fun g : G => f (Additive.toMul (z.val g) : M)) := by
    refine ⟨f m, ?_⟩
    intro g
    rw [← hf, ← map_div, hm g]
    rfl
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁ h).property

def coefficientMap : H1 G M →+ H1 G N :=
  QuotientAddGroup.lift (forgetCocycles G M).ker (mappedClass G M N f hf hc)
    (mappedClass_kernel G M N f hf hc)

theorem coefficientMap_classMap (z : continuousCocycles G M) :
    coefficientMap G M N f hf hc (classMap G M z) =
      classMap G N (mapContinuousCocycles G M N f hf hc z) := rfl


end MazurTransfer.ContinuousFirstCohomologyCoefficientMap
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.mapCocycle
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.mapContinuousCocycles
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.mappedClass
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.mappedClass_kernel
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.coefficientMap
#print axioms MazurTransfer.ContinuousFirstCohomologyCoefficientMap.coefficientMap_classMap


