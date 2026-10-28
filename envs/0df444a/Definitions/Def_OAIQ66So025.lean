-- Prove2me | Definitions.Def_OAIQ66So025
-- name    : OAIQ66So025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:31:38.248318+00:00
-- url     : https://prove2.me/theorems/f00c2686-4975-476e-9529-68f0e87d3bba
-- title:
--   Definitions bundle OAIQ66So025 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 58 definitions, 4 instances and 55 theorems. The definitions and types are `OAI.ListChains.groupHomologyProductQuotientIso`, `OAI.ListChains.pathSubgroup`, `OAI.ListChains.productHomologyQuotientEquiv`, `OAI.ListChains.productScHomologyQuotientIso`, `OAI.ListChains.productShiftSc`, `OAI.ListChains.shiftCycles`, `OAI.ListChains.shiftHomology`, `OAI.ListChains.standardShift`, `OAI.ListChains.standardShiftChainMap`, `OAI.NoncommElementary.compressed`, `OAI.OrderBrown.C`, `OAI.OrderBrown.d`, `OAI.OrderBrown.permIso`, `OAI.OrderChains.ExactIn`, `OAI.OrderChains.ExactSet`, `OAI.OrderChains.comparison`, `OAI.OrderChains.cycleFill`, `OAI.OrderChains.deleteCarrier`, `OAI.OrderChains.lowerCarrier`, `OAI.OrderChains.lowerStar`, `OAI.OrderChains.onSet`, `OAI.OrderChains.starCarrier`, `OAI.OrderListChains.based`, `OAI.OrderListChains.contraction`, `OAI.OrderListChains.finiteVertices`, `OAI.OrderListChains.vertexSupport`, `OAI.PresentationGeometry.Cells.boundaryProductEquiv`, `OAI.PresentationGeometry.PresentationComplex.transportedGenerators`, `OAI.ProductCoefficient.productAffineShift`, `OAI.ProductCoefficient.unitEquiv`, `OAI.RegularProduct.coordinateEquiv`, `OAI.RegularProduct.restrictionChainIso`, `OAI.RegularProduct.restrictionIso`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.G₁`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.G₂`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.X₁`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.X₂`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.base`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.first`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.instPrimcodableG₂` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_CategoryTheoryShortComplex`, `FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`, `FiniteType_CoreDeckLeftQuotientCovering`, `FiniteType_CosetCoordinates`, `FiniteType_CoveringCellGeometryHausdorff`, `FiniteType_EquivariantOrderChains`, `FiniteType_InducedFree`, `FiniteType_ListChainsFromTuplesCone`, `FiniteType_ListChainsMapChainComp`, `FiniteType_ListChainsShiftOrigin`, `FiniteType_OrderChains`, `FiniteType_OrderChainsOnSet`, `FiniteType_OrderListChains`, `FiniteType_OrderListChainsBased`, `FiniteType_OrderListChainsVertexSupport`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryCellCoverExtension`, `FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic`, `FiniteType_PresentationGeometryCells`, `FiniteType_PresentationGeometryDescend`, `FiniteType_ProductCoefficientAffineShift`, `FiniteType_RegularCoverGeometry`, `FiniteType_SphereCover`, `FiniteType_StageConstruction`, `FiniteType_SteinbergSixThree`, `FiniteType_TwistedBrin`, `FiniteType_TwistedBrinBasisCutBasis`, `SimpleOvergroups_DoubleEffective`, `SimpleOvergroups_EnlargementEffective`, `SimpleOvergroups_EnlargementNames`, `SimpleOvergroups_FirstFamilies`.
--
--   **Imports.** It imports the bundles `OAIQ66So017`, `OAIQ66So018`, `OAIQ66So019` and `OAIQ66So020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So027`, `OAIQ66So028` and `OAIQ66So029`; the statement `OAI.OrderBrown.vanishing`; the proof of `OAI.RegularProduct.coset_parent_local_nilpotence`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So017
import Definitions.Def_OAIQ66So018
import Definitions.Def_OAIQ66So019
import Definitions.Def_OAIQ66So020

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace PresentationComplex

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

instance instCWComplexSpaceUniv : CWComplex (univ : Set (Space w)) :=
  Cells.cwComplex (AttachingLoops.relators w) (Rose.dimension k)

instance instFiniteSpaceUnivEmptyCollectionSet : RelCWComplex.Finite (univ : Set (Space w)) :=
  Cells.cwComplex_finite (AttachingLoops.relators w) (Rose.dimension k)

instance instPathConnectedSpaceSpace : PathConnectedSpace (Space w) :=
  Cells.pathConnectedSpace (AttachingLoops.relators w) (by decide)

theorem dimension (n : ℕ) (i : RelCWComplex.cell (univ : Set (Space w)) n) : n < 3 := by
  change Cells.NewCell (X := Rose.Space k) (k := r) (d := 2) n at i
  rcases i with i | ⟨i, ⟨h⟩⟩
  · have := Rose.dimension k n i
    omega
  · omega

end PresentationComplex

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryDescend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationGeometry
namespace Cells

open Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_contractible (i : Fin k) : ContractibleSpace (cellInterior f i) := by
  let : ContractibleSpace (OpenDisk d) :=
    (convex_ball (0 : Fin d → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  exact (characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm.contractibleSpace

omit [T2Space X] [CompactSpace X] in
theorem collar_inter_interior (i : Fin k) :
    collar f ∩ cellInterior f i =
      characteristic f i '' {v : Fin d → ℝ | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1} := by
  ext z
  constructor
  · rintro ⟨hz, ⟨v, rfl⟩⟩
    refine ⟨v.1, ⟨?_, mem_ball_zero_iff.mp v.2⟩, rfl⟩
    change characteristic f i v.1 ∈ collar f at hz
    rw [characteristic_on_openDisk f i v] at hz
    exact (mem_collar_disk_iff f i (interiorInDisk v)).mp hz
  · rintro ⟨v, hv, rfl⟩
    let u : OpenDisk d := ⟨v, mem_ball_zero_iff.mpr hv.2⟩
    refine ⟨?_, ⟨u, rfl⟩⟩
    rw [show v = (interiorInDisk u).1 from rfl, characteristic_on_disk]
    exact (mem_collar_disk_iff f i (interiorInDisk u)).mpr hv.1

omit [T2Space X] [CompactSpace X] in
theorem collar_inter_interior_pathConnected (hd : 1 < d) (i : Fin k) :
    IsPathConnected (collar f ∩ cellInterior f i) := by
  rw [collar_inter_interior]
  apply (annulus_pathConnected hd).image'
  apply (characteristic_continuousOn f i).mono
  intro v hv
  exact mem_closedBall_zero_iff.mpr (le_of_lt hv.2)

theorem collar_fundamentalGroupMap_surjective (hd : 1 < d) (b : collar f) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(collar f, Space f)) b) := by
  apply PresentationVanKampen.fundamentalGroupMap_surjective_of_disjoint_open_cover
    (collar f) (cellInterior f) (collar_isOpen f) (cellInterior_isOpen f)
    (collar_union_interiors f) (cellInterior_pairwiseDisjoint f)
    (collar_inter_interior_pathConnected f hd)
  intro i
  let := cellInterior_contractible f i
  infer_instance

end Cells
end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCells
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k d : ℕ} (f : C(boundary k d, X)) (b : X) (Z : FiberBundleCore ι X Q)

variable (pot : ι → X → Q)
variable (s : C(boundary k d,Z.TotalSpace))
variable (hs : ∀ c, Z.proj (s c) = f c)

variable (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

theorem coveringCore_isCoveringMap :
    IsCoveringMap (coveringCore f b Z pot s hs hpot).proj := FiberBundle.isCoveringMap

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval

namespace PresentationGeometry.Cells
open Set Metric Topology

def boundaryProductEquiv (k d : ℕ) : boundary k d ≃ₜ Fin k × SphereCover.Sphere (Fin d → ℝ) where
  toEquiv :=
    { toFun := fun z => (z.1.1,⟨z.1.2.1,z.2⟩)
      invFun := fun z => ⟨(z.1,⟨z.2.1,sphere_subset_closedBall z.2.2⟩),z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)).subtype_mk _

end PresentationGeometry.Cells

open scoped unitInterval
open Set

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RegularCoverGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma oldLift_fiber_bijective (x : X) : Function.Bijective
    (CoveringMapNatural.fiberMap (p := Z.proj)
      (⟨Adjunction.old f,Adjunction.continuous_old f⟩ : C(X,Cells.Space f))
      (oldLift f b Z pot s hs hpot) (funext (oldLift_proj f b Z pot s hs hpot)) x) :=
  FiberCoreMap.fiber_bijective Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q) x

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Function Topology
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
open Set Topology unitInterval
namespace PresentationGeometry.CellCoverExtension
open Set Cells Metric
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma oldLift_isEmbedding : IsEmbedding (oldLift f b Z pot s hs hpot) :=
  FiberCoreMap.isEmbedding Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q)
    (Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding

lemma range_oldLift : Set.range (oldLift f b Z pot s hs hpot) =
    (coveringCore f b Z pot s hs hpot).proj ⁻¹' Set.range (Adjunction.old f) := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨Z.proj a,rfl⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := (oldLift_fiber_bijective f b Z pot s hs hpot x).2 ⟨z,hx.symm⟩
    exact ⟨a.1,congrArg Subtype.val ha⟩

end PresentationGeometry.CellCoverExtension

end

open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometryHausdorff
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.Cells
open Set Metric Topology
variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
  [CWComplex (univ : Set X)] [RelCWComplex.FiniteType (univ : Set X)]
  {k d : ℕ} (f : C(boundary k d,X))
  (hdim : ∀ n, RelCWComplex.cell (univ : Set X) n → n < d)

lemma skeleton_eq_old :
    letI := cwComplex f hdim
    (RelCWComplex.skeletonLT (univ : Set (Space f)) d : Set (Space f)) =
      Set.range (Adjunction.old f) := by
  let := cwComplex f hdim
  ext z
  constructor
  · intro hz
    obtain ⟨n,hn,c,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp hz
    rcases c with c | ⟨i,⟨rfl⟩⟩
    · exact ⟨RelCWComplex.map n c v,rfl⟩
    · exact absurd hn (lt_irrefl _)
  · rintro ⟨x,rfl⟩
    have hx : x ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
        RelCWComplex.openCell n i := by
      rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    simp only [mem_iUnion,RelCWComplex.openCell,mem_image] at hx
    obtain ⟨n,c,v,hv,hx⟩ := hx
    exact CWComplex.mem_skeletonLT_iff.mpr
      ⟨n,by exact_mod_cast hdim n c,Sum.inl c,v,hv,congrArg (Adjunction.old f) hx⟩
end PresentationGeometry.Cells

namespace SingularChains
open _root_.CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
lemma homologyMap_of_homotopic {f g : C(X,Y)} (h : f.Homotopic g) (j : ℕ) :
    homologyMap (map f) j = homologyMap (map g) j :=
  (show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from h.some).singularChainComplexFunctorObjMap
    (ModuleCat.of ℤ ℤ) |>.homologyMap_eq j

lemma homologyMap_const_zero (j : ℕ) (hj : j ≠ 0) (y : Y) :
    homologyMap (map (ContinuousMap.const X y)) j = 0 := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) j).obj (ModuleCat.of ℤ ℤ)
  have hz : CategoryTheory.Limits.IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) j (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hj
  change F.map (TopCat.ofHom (ContinuousMap.const X y)) = 0
  have he : TopCat.ofHom (ContinuousMap.const X y) =
      TopCat.ofHom (ContinuousMap.const X PUnit.unit) ≫
        TopCat.ofHom (ContinuousMap.const PUnit y) := rfl
  rw [he,F.map_comp,hz.eq_of_src (F.map (TopCat.ofHom (ContinuousMap.const PUnit y))) 0,comp_zero]
end SingularChains

namespace PresentationGeometry.CellCoverExtension
open Set Topology Cells CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

variable [Nonempty X] [CWComplex (univ : Set X)]
  [RelCWComplex.FiniteType (univ : Set X)]
  (hdim : ∀ m, RelCWComplex.cell (univ : Set X) m → m < d)
include hdim

lemma oldLift_skeleton :
    letI := Cells.cwComplex f hdim
    letI := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
    letI := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
    Set.range (oldLift f b Z pot s hs hpot) =
      Skel (univ : Set (coveringCore f b Z pot s hs hpot).TotalSpace) d := by
  let := Cells.cwComplex f hdim
  let := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
  let := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
  rw [range_oldLift]
  change _ = (RelCWComplex.skeletonLT (univ : Set (coveringCore f b Z pot s hs hpot).TotalSpace) d : Set (coveringCore f b Z pot s hs hpot).TotalSpace)
  rw [CoveringCW.skeleton_preimage,Cells.skeleton_eq_old f hdim]

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationGeometry.CellCoverExtension
open Set Cells Metric _root_.CategoryTheory HomologicalComplex SingularChains
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma any_attaching_lift_nullhomotopic {n : ℕ} (hd : d = n+3) (i : Fin k)
    (t : C(SphereCover.Sphere (Fin d → ℝ),Z.TotalSpace))
    (ht : ∀ v, Z.proj (t v) = f (boundarySlice i v)) :
    ∃ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      ((oldLift f b Z pot s hs hpot).comp t).Homotopic (ContinuousMap.const _ z) := by
  subst d
  let : SimplyConnectedSpace (SphereCover.Sphere (Fin (n+3) → ℝ)) :=
    SphereCover.normed_simplyConnected n (by simp)
  let : ContractibleSpace (Disk (n+3)) := Metric.contractibleSpace_closedBall (by norm_num)
  exact CoveringCellGeometry.boundary_nullhomotopic
    (coveringCore_isCoveringMap f b Z pot s hs hpot) (attachedDisk f i) sphereInDisk
    ((oldLift f b Z pot s hs hpot).comp t)
    (by
      funext v
      exact (congrArg (Adjunction.old f) (ht v)).trans (attachedDisk_boundary f i v).symm)
    (Classical.arbitrary _)

lemma any_attaching_homology_killed {n : ℕ} (hd : d = n+3) (i : Fin k)
    (t : C(SphereCover.Sphere (Fin d → ℝ),Z.TotalSpace))
    (ht : ∀ v, Z.proj (t v) = f (boundarySlice i v)) (j : ℕ) (hj : j ≠ 0) :
    homologyMap (map t) j ≫ homologyMap (map (oldLift f b Z pot s hs hpot)) j = 0 := by
  obtain ⟨z,hz⟩ := any_attaching_lift_nullhomotopic f b Z pot s hs hpot hd i t ht
  rw [← homologyMap_comp,← map_comp,homologyMap_of_homotopic hz,homologyMap_const_zero j hj z]

lemma deck_attaching_homology_killed {n : ℕ} (hd : d = n+3) (i : Fin k) (q : Q)
    (j : ℕ) (hj : j ≠ 0) :
    homologyMap (map (s.comp (boundarySlice i))) j ≫
      homologyMap (map (⟨CoreDeck.right Z q,CoreDeck.continuous_right Z (CoreDeck.of_potential Z pot hpot) q⟩ : C(Z.TotalSpace,Z.TotalSpace))) j ≫
        homologyMap (map (oldLift f b Z pot s hs hpot)) j = 0 := by
  rw [← Category.assoc,← homologyMap_comp,← map_comp]
  apply any_attaching_homology_killed f b Z pot s hs hpot hd i _ _ j hj
  intro v
  exact hs (boundarySlice i v)
end PresentationGeometry.CellCoverExtension

open Set Topology Metric

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.PresentationComplex
open DiscreteCoverCharts
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable (eQ : Q ≃* PresentedGroup (relatorSet w))
def transportedGenerators : Fin k → Q := fun i => eQ.symm (PresentedGroup.of i)
omit [TopologicalSpace Q] [DiscreteTopology Q] in
lemma lift_transportedGenerators : FreeGroup.lift (transportedGenerators w eQ) =
    eQ.symm.toMonoidHom.comp (PresentedGroup.mk (relatorSet w)) := by
  apply FreeGroup.ext_hom
  intro i
  rw [FreeGroup.lift_apply_of]
  rfl
omit [TopologicalSpace Q] [DiscreteTopology Q] in
lemma transported_relators (i : Fin r) :
    FreeGroup.lift (transportedGenerators w eQ) (FreeGroup.mk (w i)) = 1 := by
  have h : PresentedGroup.mk (relatorSet w) (FreeGroup.mk (w i)) = 1 :=
    PresentedGroup.one_of_mem ⟨i,rfl⟩
  rw [lift_transportedGenerators,MonoidHom.comp_apply,h,map_one]
end PresentationGeometry.PresentationComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains

section

variable (G : Type*) [Group G]

def pathSubgroup (A : Set G) : Subgroup G where
  carrier := {g | FillsAt G A 0 (vertex G g - vertex G 1)}
  one_mem' := ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,by simp⟩
  mul_mem' := by
    rintro g h ⟨c,hcd,hc,dc⟩ ⟨d,hdd,hd,dd⟩
    refine ⟨c + mapChain G (fun x => g*x) d,
      Submodule.add_mem _ hcd (mapChain_mem_degree G _ hdd),
      Submodule.add_mem _ hc (leftTranslate_mem_controlled G g hd),?_⟩
    rw [map_add,dc,boundary_mapChain,dd,map_sub,mapChain_vertex,mapChain_vertex,mul_one]
    abel
  inv_mem' := by
    rintro g ⟨c,hcd,hc,dc⟩
    refine ⟨-mapChain G (fun x => g⁻¹*x) c,
      Submodule.neg_mem _ (mapChain_mem_degree G _ hcd),
      Submodule.neg_mem _ (leftTranslate_mem_controlled G g⁻¹ hc),?_⟩
    rw [map_neg,boundary_mapChain,dc,map_sub,mapChain_vertex,mapChain_vertex,
      inv_mul_cancel,mul_one]
    abel

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsShiftOrigin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains

section

variable (G I C : Type*) [Group G]

lemma productShift_mem_cycles (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ productCycles G I C n) :
    productShift G I C f σ δ z ∈ productCycles G I C n := by
  refine ⟨productShift_mem_chains G I C f σ δ hz.1,?_⟩
  change productBoundary G I C _ = 0
  rw [productBoundary_shift,show productBoundary G I C z = 0 from hz.2,map_zero]

def shiftCycles (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productCycles G I C n →ₗ[ℤ] productCycles G I C n :=
  (productShift G I C f σ δ).restrict (fun _ hz => productShift_mem_cycles G I C f σ δ hz)

lemma shiftCycles_mem_boundaries (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productBoundaries G I C n ≤
      (productBoundaries G I C n).comap (shiftCycles G I C f σ δ n) := by
  rintro z ⟨w,rfl⟩
  refine ⟨shiftChains G I C f σ δ (n+1) w,?_⟩
  apply Subtype.ext
  exact productBoundary_shift G I C f σ δ w.val

def shiftHomology (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    BoundedProductHomology G I C n →ₗ[ℤ] BoundedProductHomology G I C n :=
  (productBoundaries G I C n).mapQ (productBoundaries G I C n)
    (shiftCycles G I C f σ δ n) (shiftCycles_mem_boundaries G I C f σ δ n)

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsFromTuplesCone
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace ListChains

open _root_.CategoryTheory
variable (G I C : Type) [Group G]

lemma productCycleKernelEquiv_boundaries (n : ℕ) :
    (productBoundaries G I C (n+1)).map (productCycleKernelEquiv G I C n).toLinearMap =
      LinearMap.range (productShortComplex G I C n).moduleCatToCycles := by
  rw [productBoundaries,← LinearMap.range_comp]
  rfl

def productHomologyQuotientEquiv (n : ℕ) :
    BoundedProductHomology G I C (n+1) ≃ₗ[ℤ]
      (productShortComplex G I C n).moduleCatLeftHomologyData.H :=
  Submodule.Quotient.equiv _ _ (productCycleKernelEquiv G I C n)
    (productCycleKernelEquiv_boundaries G I C n)

def groupHomologyProductQuotientIso (n : ℕ) :
    groupHomology (ProductCoefficient.rep G I C) (n+1) ≅
      ModuleCat.of ℤ (BoundedProductHomology G I C (n+1)) :=
  groupHomologyBoundedIso G I C (n+1) ≪≫
    (boundedProductComplex G I C).homologyIsoSc' (n+2) (n+1) n (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (boundedProductScIso G I C n) ≪≫
    (productShortComplex G I C n).moduleCatHomologyIso ≪≫
    (productHomologyQuotientEquiv G I C n).symm.toModuleIso

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace ProductCoefficient
variable (G I C : Type*) [Group G]

def productAffineShift (f : G →* G) (σ : C → C) (δ : C → G) :
    Module G I C →ₗ[ℤ] Module G I C :=
  LinearMap.pi (fun i => (affineShift G C f σ δ).comp (LinearMap.proj i))

@[simp] lemma productAffineShift_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (a : Module G I C) (i : I) :
    productAffineShift G I C f σ δ a i = affineShift G C f σ δ (a i) := rfl

end ProductCoefficient

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def standardShift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    Coinvariants ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ →ₗ[ℤ]
      Coinvariants ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ :=
  (standardProductEquiv G I C n).symm.toLinearMap.comp
    ((shiftChains G I C f σ δ n).comp (standardProductEquiv G I C n).toLinearMap)

def standardShiftChainMap (f : G →* G) (σ : C → C) (δ : C → G) :
    standardProductComplex G I C ⟶ standardProductComplex G I C :=
  (standardProductComplexIso G I C).hom ≫ boundedShiftChainMap G I C f σ δ ≫
    (standardProductComplexIso G I C).inv

@[simp] lemma standardShiftChainMap_f (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    (standardShiftChainMap G I C f σ δ).f n = ModuleCat.ofHom (standardShift G I C f σ δ n) := by
  change (standardProductComplexIso G I C).hom.f n ≫
      (boundedShiftChainMap G I C f σ δ).f n ≫ (standardProductComplexIso G I C).inv.f n = _
  change ModuleCat.ofHom ((standardProductEquiv G I C n).toLinearMap) ≫
      ModuleCat.ofHom (shiftChains G I C f σ δ n) ≫
      ModuleCat.ofHom ((standardProductEquiv G I C n).symm.toLinearMap) = _
  simp only [standardShift, ModuleCat.ofHom_comp, Category.assoc]

end ListChains

open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CategoryTheoryShortComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

def productShiftSc (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productShortComplex G I C n ⟶ productShortComplex G I C n where
  τ₁ := ModuleCat.ofHom (shiftChains G I C f σ δ (n+2))
  τ₂ := ModuleCat.ofHom (shiftChains G I C f σ δ (n+1))
  τ₃ := ModuleCat.ofHom (shiftChains G I C f σ δ n)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ (n+1) z
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ n z

def productScHomologyQuotientIso (n : ℕ) :
    (productShortComplex G I C n).homology ≅
      ModuleCat.of ℤ (BoundedProductHomology G I C (n+1)) :=
  (productShortComplex G I C n).moduleCatHomologyIso ≪≫
    (productHomologyQuotientEquiv G I C n).symm.toModuleIso

end ListChains

open CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetCoordinates
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits

namespace RegularProduct
section
open _root_.CategoryTheory
variable (G I : Type) [Group G]

variable (S : Subgroup G)

def coordinateEquiv : Module G I ≃ₗ[ℤ] ProductCoefficient.Module S I (G ⧸ S) :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S))

@[simp] lemma coordinateEquiv_apply (a : Module G I) (i : I) :
    coordinateEquiv G I S a i = Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (a i) := rfl

lemma coordinateEquiv_rightShift (s : S) (a : G →₀ ℤ) :
    Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (rightShift G (s : G) a) =
      ProductCoefficient.rightShift S (G ⧸ S) s (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) a) := by
  have h : (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) : (G →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap.comp
      (rightShift G (s : G)) =
    (ProductCoefficient.rightShift S (G ⧸ S) s).comp
      (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    change Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)
        (rightShift G (s : G) (Finsupp.single x r)) =
      ProductCoefficient.rightShift S (G ⧸ S) s
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (Finsupp.single x r))
    rw [rightShift_single,Finsupp.domLCongr_single,Finsupp.domLCongr_single]
    change Finsupp.single (CosetCoordinates.equiv S (x*(s : G)⁻¹)) r =
      ProductCoefficient.rightShift S (G ⧸ S) s
        (Finsupp.single ((CosetCoordinates.equiv S x).1,(CosetCoordinates.equiv S x).2) r)
    rw [ProductCoefficient.rightShift_single]
    congr 1
    exact CosetCoordinates.equiv_mul_subgroup S x s⁻¹
  exact LinearMap.congr_fun h a

def restrictionIso : Rep.res S.subtype (rep G I) ≅ ProductCoefficient.rep S I (G ⧸ S) :=
  Rep.mkIso (Representation.Equiv.mk (coordinateEquiv G I S) (by
    intro s
    apply LinearMap.ext
    intro a
    funext i
    exact coordinateEquiv_rightShift G S s (a i)))

end

open _root_.CategoryTheory

end RegularProduct

namespace RegularProduct
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

def restrictionChainIso :
    (Rep.standardComplex ℤ S).coinvariantsTensorObj (Rep.res S.subtype (rep G I)) ≅
      ListChains.standardProductComplex S I (G ⧸ S) :=
  (NatIso.mapHomologicalComplex
    ((Rep.coinvariantsTensor ℤ S).mapIso (restrictionIso G I S)) _).app _

end RegularProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Pointwise

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma swapWord_mem (i j : n) (h : i≠j) (u : Rˣ) : swapWord i j h u∈elementary :=
  (elementary (R:=R)).mul_mem ((elementary (R:=R)).mul_mem
    (root_mem _ _ _ _) (root_mem _ _ _ _)) (root_mem _ _ _ _)

lemma balanced (i j : n) (h : i≠j) (u : Rˣ) :
    swapWord i j h u*swapWord i j h (-1)=position i u*position j u⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul,swapWord_val,position_val]
  simp [mul_add,add_mul,sub_mul,mul_sub,Matrix.single_mul_single_of_ne _ _ _ _ h,
    Matrix.single_mul_single_of_ne _ _ _ _ h.symm,Matrix.single_mul_single_same,
    ← Matrix.single_neg, single_sub]
  abel

lemma balanced_mem (i j : n) (h : i≠j) (u : Rˣ) :
    position i u*position j u⁻¹∈elementary := by
  rw [← balanced i j h u]
  exact (elementary (R:=R)).mul_mem (swapWord_mem _ _ _ _) (swapWord_mem _ _ _ _)

end NoncommElementary

open scoped commutatorElement

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCoefficient
variable (G I : Type) [Group G]
def unitEquiv : Module G I PUnit.{1} ≃ₗ[ℤ] RegularProductR.Module ℤ G I :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (Equiv.punitProd G))
end ProductCoefficient

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NoncommElementary
section
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma position_commutator_mem (i j : n) (h : i≠j) (u v : Rˣ) :
    position i u*position i v*(position i u)⁻¹*(position i v)⁻¹∈elementary := by
  let a := position i u
  let b := position j u
  let c := position i v
  let r := a*b⁻¹
  have hr : r∈elementary := by simpa only [r,a,b,map_inv] using balanced_mem i j h u
  have hbc : Commute b c := positions_commute j i h.symm u v
  have hmove : b⁻¹*c*b=c := by rw [hbc.inv_left.eq]; group
  have heq : r*(c*r⁻¹*c⁻¹)=a*c*a⁻¹*c⁻¹ := by
    calc r*(c*r⁻¹*c⁻¹)=a*(b⁻¹*c*b)*a⁻¹*c⁻¹ := by dsimp [r]; group
         _ = a*c*a⁻¹*c⁻¹ := by rw [hmove]
  rw [← heq]
  apply (elementary (R:=R)).mul_mem hr
  exact (Subgroup.mem_normalizer_iff.mp (position_normalizes i v) r⁻¹).mp
    ((elementary (R:=R)).inv_mem hr)

lemma quotient_commute (i j : n) (h : i≠j) (u v : Rˣ) :
    Commute (QuotientGroup.mk' (diagonalKernel i) u) (QuotientGroup.mk' (diagonalKernel i) v) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  change position i (u*v*u⁻¹*v⁻¹)∈elementary
  simp only [map_mul,map_inv]
  exact position_commutator_mem i j h u v

lemma quotient_conjugate (i j : n) (h : i≠j) (u v : Rˣ) :
    QuotientGroup.mk' (diagonalKernel i) (u*v*u⁻¹)=QuotientGroup.mk' (diagonalKernel i) v := by
  simp only [map_mul,map_inv]
  rw [quotient_commute i j h u v |>.eq]
  simp [mul_assoc]

end

variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

theorem compressed_diagonal (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) (u : Rˣ) :
    position i (NonunitalCompression.units φ u) ∈ elementary := by
  have hz := D.annihilates (QuotientGroup.mk' (diagonalKernel (R:=R) i))
    (quotient_conjugate i j h) u
  rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff] at hz
  exact hz

def compressed (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) : Rˣ →* elementary (R:=R) (n:=n) where
  toFun u := ⟨position i (NonunitalCompression.units φ u),compressed_diagonal φ D i j h u⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' u v := by apply Subtype.ext; simp

@[simp] lemma compressed_coe (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) (u : Rˣ) :
    (compressed φ D i j h u : (Matrix n n R)ˣ)=position i (NonunitalCompression.units φ u) := rfl

end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
lemma units_injective (φ : R →ₙ+* S) (hφ : Function.Injective φ) :
    Function.Injective (units φ) := by
  intro u v h
  apply Units.ext
  have he := congrArg Units.val h
  change 1+φ (u.val-1)=1+φ (v.val-1) at he
  exact sub_left_injective (hφ (add_left_cancel he))
end NonunitalCompression

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

def Refines (B C : Basis ρ) : Prop :=
  ∀ c : C, ∃ b : B, GermBrick.Restricts ρ c.1 b.1

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains

variable (G : Type*)

lemma head_mem_vertices (s : Simplex G) : s.1 ∈ vertices G s := Or.inl rfl

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
variable (G : Type*)
def based : OrderBasedComplex.Data (Simplex G) where
  degree := degree G
  d := boundary G
  aug := augmentation G
  d_squared := boundary_boundary G
  lowers := boundary_lowers G
  aug_single s := by simp only [augmentation_single, degree, List.length_eq_zero_iff]
  aug_d := augmentation_boundary G

def contraction (a : G) : OrderBasedComplex.Contraction (boundary G) (augmentation G) where
  point := vertex G a
  cone := cone G a
  d_point := boundary_vertex G a
  aug_point := augmentation_vertex G a
  aug_cone := augmentation_cone G a
  identity c := by rw [boundary_cone, K_apply]; abel

end OrderListChains

namespace OrderListChains
variable (V : Type*)

lemma mem_list (s : Simplex V) (v : V) : v ∈ list V s ↔ v ∈ vertices V s := by
  simp only [list,List.mem_cons,mem_vertices]

noncomputable def finiteVertices (s : Simplex V) : Finset V := by
  classical
  exact (list V s).toFinset
lemma finiteVertices_nonempty (s : Simplex V) : (finiteVertices V s).Nonempty := by
  classical
  exact ⟨s.1,by simp [finiteVertices,list]⟩
lemma mem_finiteVertices (s : Simplex V) (v : V) :
    v ∈ finiteVertices V s ↔ v ∈ vertices V s := by
  classical
  simp only [finiteVertices,List.mem_toFinset,mem_list]

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]

variable {Q : Type*} [Preorder Q]

noncomputable def comparison (f g : P →o Q) : Chain P →ₗ[ℤ] Chain Q :=
  OrderBasedComplex.homotopy (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g)

def ExactIn (n : ℕ) : Prop := ∀ c : Chain P, c ∈ module P → Homogeneous P n c →
  boundary P c = 0 → augmentation P c = 0 →
  ∃ d : Chain P, d ∈ module P ∧ Homogeneous P (n+1) d ∧ boundary P d = c

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsOnSet
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
def onSet (U : Set P) : Submodule ℤ (Chain P) :=
  Finsupp.supported ℤ ℤ {s | Descending P s ∧ vertices P s ⊆ U}

def ExactSet (U : Set P) (n : ℕ) : Prop := ∀ c : Chain P, c ∈ onSet P U →
  Homogeneous P n c → boundary P c = 0 → augmentation P c = 0 →
  ∃ d : Chain P, d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧ boundary P d = c

noncomputable def cycleFill (U : Set P) (n : ℕ) (c : Chain P) : Chain P := by
  classical
  exact if h : ∃ d : Chain P, d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧ boundary P d = c
    then Classical.choose h else 0
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
noncomputable def deleteCarrier (U : Set P) (a : P) (s : Simplex P) : Set P := by
  classical
  exact if a ∈ vertices P s then {x | x ∈ U ∧ a < x} else vertices P s
noncomputable def starCarrier (U : Set P) (a : P) (s : Simplex P) : Set P := by
  classical
  exact if a ∈ vertices P s then {x | x ∈ U ∧ a ≤ x} else vertices P s
end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsVertexSupport
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
variable (P : Type*)
noncomputable def vertexSupport (c : Chain P) : Finset P := by
  classical
  exact c.support.biUnion (fun s => (list P s).toFinset)
end OrderListChains

namespace OrderChains

open OrderListChains
variable (P : Type*) [PartialOrder P]
noncomputable def lowerCarrier (r : P → ℕ) (h : ℕ) (s : Simplex P) : Set P :=
  if r s.1 = h+1 then Set.Iio s.1 else vertices P s
noncomputable def lowerStar (r : P → ℕ) (h : ℕ) (s : Simplex P) : Set P :=
  if r s.1 = h+1 then Set.Iic s.1 else vertices P s

end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChainComplex
open OrderListChains
variable (P : Type) [Preorder P]

instance instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains (n : ℕ) : Module.Free ℤ (chains P n) := Module.Free.of_equiv (basisIso P n).symm

end OrderChainComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_EquivariantOrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex

attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule

end EquivariantOrderChains

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open OrderChainComplex EquivariantOrderChains
variable {G P I : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] [Nonempty P]

def permIso (n : ℕ) : object (G := G) (P := P) n ≅ OrbitBrown.perm G (simplexSet P n) :=
  permutationIso n ≪≫ Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) (fun g => by
    apply Finsupp.lhom_ext
    intro s r
    change Finsupp.mapDomain (g • ·) (Finsupp.single s r) =
      FunctionalTree.diagonalAction (Rep.trivial ℤ G ℤ) g (Finsupp.single s r)
    rw [Finsupp.mapDomain_single, FunctionalTree.diagonalAction_single]
    rfl))

def C : ℕ → Rep ℤ G
  | 0 => Rep.trivial ℤ G ℤ
  | n+1 => object (G := G) (P := P) n
def d : (n : ℕ) → C (G := G) (P := P) (n+1) ⟶ C (G := G) (P := P) n
  | 0 => augmentation
  | n+1 => differential n
end OrderBrown

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementNames
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
noncomputable section
namespace Coeff
open BinaryPrefixOperators.Arithmetic
variable {k : Type*} [CommRing k]
@[simp] theorem value_mul (a b : Name k) : value (mul a b) = value a * value b := Lists.value_product a b
@[simp] theorem value_complement (a : Name k) : value (complement a) = 1-value a := by
  simp [complement,sub_eq_add_neg]
end Coeff
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)

variable (e : P → Coeff.Name k)

def rootArray (a : P × G) : Array.Name (Coeff.Name k) G :=
  [(Coeff.complement (e a.1),N.one),(e a.1,a.2)]

def array (w : Word P G) : Array.Name (Coeff.Name k) G :=
  w.foldr (fun a p => Array.product Coeff.mul N.mul (rootArray N e a) p) [(Coeff.one,N.one)]

def pointArray (x : Point P G X) : Array.Name (Coeff.Name k) X :=
  Array.product Coeff.mul N.act (array N e x.1) [(Coeff.one,x.2)]

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  {C : ActionCalculus V Y K L m} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

abbrev D (k : Type*) [CommRing k] := BinaryPrefixOperators.algebra k

def rootValue (a : P × G) : (MonoidAlgebra (D k) V)ˣ :=
  SourceEnlargement.unitMap (Coeff.value (e a.1)) (he a.1) (I.group a.2).val

def groupValue (w : Word P G) : (MonoidAlgebra (D k) V)ˣ := (w.map (rootValue N e I he)).prod

omit [Nonempty Y] in
@[simp] theorem groupValue_nil : groupValue N e I he [] = 1 := rfl
omit [Nonempty Y] in
@[simp] theorem groupValue_cons (a : P × G) (w : Word P G) :
    groupValue N e I he (a::w) = rootValue N e I he a * groupValue N e I he w := rfl
omit [Nonempty Y] in
@[simp] theorem groupValue_append (a b : Word P G) :
    groupValue N e I he (a++b) = groupValue N e I he a * groupValue N e I he b := by simp [groupValue]

omit [Nonempty Y] in
@[simp] theorem rootValue_inv (a : P × G) :
    rootValue N e I he (rootInv N a) = (rootValue N e I he a)⁻¹ := by
  simp only [rootValue,rootInv,I.inv]
  exact map_inv _ _

omit [Nonempty Y] in
@[simp] theorem groupValue_inverse (w : Word P G) :
    groupValue N e I he (inverse N w) = (groupValue N e I he w)⁻¹ := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih,mul_inv_rev]

def pointValue (x : Point P G X) : Y →₀ D k :=
  groupValue N e I he x.1 • Finsupp.single (I.point x.2).val 1

omit [Nonempty Y] in
@[simp] theorem pointValue_act (w : Word P G) (x : Point P G X) :
    pointValue N e I he (w++x.1,x.2) =
      @SMul.smul _ _ SourceEnlargement.unitsAction.toSMul (groupValue N e I he w) (pointValue N e I he x) := by
  simp only [pointValue,groupValue_append,mul_smul]
  rfl

omit [Nonempty Y] in
@[simp] theorem value_rootArray (a : P × G) :
    Array.algebraValue Coeff.value (fun g => (I.group g).val) (rootArray N e a) =
      (rootValue N e I he a).val := by
  simp only [rootArray,Array.algebraValue_cons,Array.algebraValue_nil,add_zero,Coeff.value_complement,I.one]
  rfl

omit [Nonempty Y] in
@[simp] theorem value_array (w : Word P G) :
    Array.algebraValue Coeff.value (fun g => (I.group g).val) (array N e w) =
      (groupValue N e I he w).val := by
  induction w with
  | nil => simp only [array,List.foldr_nil,Array.algebraValue_cons,Array.algebraValue_nil,add_zero,
      I.one,Coeff.value_one]; rfl
  | cons a w ih =>
    change Array.algebraValue _ _ (Array.product Coeff.mul N.mul (rootArray N e a) (array N e w)) = _
    rw [Array.algebraValue_product _ _ _ _ Coeff.value_mul (fun g h => congrArg WithBound.val (I.mul g h)),
      value_rootArray N e I he,ih]
    rfl

omit [Nonempty Y] in
@[simp] theorem value_pointArray (x : Point P G X) :
    Array.value Coeff.value (fun x => (I.point x).val) (pointArray N e x) = pointValue N e I he x := by
  unfold pointArray
  rw [Array.value_action _ _ _ _ _ Coeff.value_mul (fun g x => congrArg WithBound.val (I.act g x)),
    value_array N e I he]
  simp only [Array.value_cons,Array.value_nil,add_zero,Coeff.value_one]
  rfl

end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementEffective
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
open BinaryPrefixOperators.Arithmetic
noncomputable section
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)
  (e : P → Coeff.Name k)
variable [Primcodable k]

def arrayKey {J : Type*} [Primcodable J] : (J →₀ D k) → ℕ :=
  semanticKey (Array.value Coeff.value id)
    (Array.value_surjective Coeff.value id Lists.value_surjective Function.surjective_id)

 theorem arrayKey_injective {J : Type*} [Primcodable J] :
    Function.Injective (arrayKey (k:=k) (J:=J)) := semanticKey_injective _ _

def pairedKey {J : Type*} [Primcodable J] (p : (J →₀ D k) × (J →₀ D k)) : ℕ × ℕ :=
  (arrayKey p.1,arrayKey p.2)

 theorem pairedKey_injective {J : Type*} [Primcodable J] :
    Function.Injective (pairedKey (k:=k) (J:=J)) := by
  intro p q h
  exact Prod.ext (arrayKey_injective (congrArg Prod.fst h)) (arrayKey_injective (congrArg Prod.snd h))

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  (C : ActionCalculus V Y K L m) [Primcodable K] [Primcodable L]

def calculus : ActionCalculus (MonoidAlgebra (D k) V)ˣ (Y →₀ D k) (ℕ × ℕ) ℕ m :=
  (C.enlargement (D k)).rekey pairedKey arrayKey pairedKey_injective arrayKey_injective

variable {C} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

variable [Primcodable G] [Primcodable X]

def partialGroupKey (f : G → Part K) (w : Word P G) : Part (ℕ × ℕ) :=
  (Array.collectedKey Coeff.value f (array N e w)).bind fun a =>
    (Array.collectedKey Coeff.value f (array N e (inverse N w))).map fun b => (a,b)

def partialPointKey (f : X → Part L) (x : Point P G X) : Part ℕ :=
  Array.collectedKey Coeff.value f (pointArray N e x)

variable [Primcodable P] [Finite P] [Finite k]

omit [Finite P] in
 theorem primrec_act : Primrec₂ ((operations (P:=P) N).act) :=
  (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)


end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_DoubleEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Double
open BoundedEncoding NamedAction
noncomputable section
open scoped Classical

variable {A k₀ k₁ k₂ P₁ P₂ : Type*}
  [CommRing k₀] [CommRing k₁] [CommRing k₂]
  [Primcodable A] [Primcodable k₀] [Primcodable k₁] [Primcodable k₂]
  [Finite k₀] [Finite k₁] [Finite k₂]
  [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
  {n : ℕ}

abbrev G₁ (P k A : Type*) (n : ℕ) := Enlargement.Word P (G₀ k A n)
abbrev X₁ (P k A : Type*) (n : ℕ) := Enlargement.Point P (G₀ k A n) (X₀ k A n)
abbrev G₂ (P₁ P₂ k A : Type*) (n : ℕ) := Enlargement.Word P₂ (G₁ P₁ k A n)
abbrev X₂ (P₁ P₂ k A : Type*) (n : ℕ) := Enlargement.Point P₂ (G₁ P₁ k A n) (X₁ P₁ k A n)

abbrev base (grade : List A → ℕ) := MatrixWords.nameOperations (k:=k₀) (n:=n) grade
abbrev first (grade : List A → ℕ) := Enlargement.operations (P:=P₁) (base (k₀:=k₀) (n:=n) grade)
abbrev operations (grade : List A → ℕ) :=
  Enlargement.operations (P:=P₂) (first (P₁:=P₁) (k₀:=k₀) (n:=n) grade)

variable (e₁ : P₁ → Enlargement.Coeff.Name k₁) (e₂ : P₂ → Enlargement.Coeff.Name k₂)
variable (grade : List A → ℕ) (omega : List A) (f : List A → Part (List A))

def partialGroupKey : G₂ P₁ P₂ k₀ A n → Part (ℕ × ℕ) :=
  Enlargement.partialGroupKey (first grade) e₂
    (Enlargement.partialGroupKey (base grade) e₁
      (MatrixWords.partialGroupKey (k:=k₀) (n:=n) omega f))

def partialPointKey : X₂ P₁ P₂ k₀ A n → Part ℕ :=
  Enlargement.partialPointKey (first grade) e₂
    (Enlargement.partialPointKey (base grade) e₁
      (MatrixWords.partialPointKey (k:=k₀) (n:=n) omega f))

def test (w : List (Letter (G₂ P₁ P₂ k₀ A n) (X₂ P₁ P₂ k₀ A n))) :
    Part (Result (ℕ × ℕ) ℕ) :=
  (operations grade).test (partialGroupKey e₁ e₂ grade omega f)
    (partialPointKey e₁ e₂ grade omega f) w

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
attribute [local instance] WordCalculus.rawMatrixAction

variable (he₁ : ∀ p, Enlargement.Coeff.value (e₁ p) * Enlargement.Coeff.value (e₁ p) =
    Enlargement.Coeff.value (e₁ p))
  (he₂ : ∀ p, Enlargement.Coeff.value (e₂ p) * Enlargement.Coeff.value (e₂ p) =
    Enlargement.Coeff.value (e₂ p))


local instance instPrimcodableG₂ : Primcodable (G₂ P₁ P₂ k₀ A n) := inferInstance
local instance instPrimcodableX₂ : Primcodable (X₂ P₁ P₂ k₀ A n) := inferInstance

 theorem primrec_inv_base : Primrec ((base (k₀:=k₀) (n:=n) grade).inv) := MatrixWords.primrec_inverse
end
end SimpleFInftyOvergroups.EffectiveNames.Double

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FirstFamilies
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

namespace GroupFamily
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)

theorem partrec_test (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    Partrec (test s) :=
  (Primrec.option_some.to_comp.comp (WordProblem.computable_testedClass s h)).partrec

end GroupFamily

namespace ProductFamily
variable {A : Type*}

variable [DecidableEq A]

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

variable [Primcodable A]

theorem partrec_test {P : Type*} [Primcodable P] {f : P → List A → Part (List A)}
    (zero : List A) (hf : Partrec₂ f) : Partrec₂ (fun p => test zero (f p)) := by
  have hp : Partrec₂ (fun p (w : List (Letter A)) => f p (Projection.left w)) :=
    hf.comp Computable.fst (Projection.primrec_left.to_comp.comp Computable.snd)
  exact (hp.map ((primrec_combine zero).to_comp.comp
    (Computable.snd.pair (PartialAffine.computable_testedClass.comp
      (Projection.primrec_right.to_comp.comp (Computable.snd.comp Computable.fst))))).to₂).to₂
end ProductFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end


