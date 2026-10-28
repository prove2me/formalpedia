-- Prove2me | Definitions.Def_OAIQ66So027
-- name    : OAIQ66So027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:34:40.092964+00:00
-- url     : https://prove2.me/theorems/7f1485ad-1a80-4363-bb4d-722daf3f89fe
-- title:
--   Definitions bundle OAIQ66So027 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 118 declarations of OpenAI's Lean: 44 definitions, 1 inductive type or structure, 4 instances and 69 theorems. The definitions and types are `OAI.CWEquivariant.boundaryIntertwiner`, `OAI.CWEquivariant.complex`, `OAI.CWEquivariant.cyclesEquiv`, `OAI.CWEquivariant.cyclesMap`, `OAI.CWEquivariant.differential`, `OAI.CWEquivariant.moduleBoundary`, `OAI.CWEquivariant.qLinear`, `OAI.CWEquivariant.qRep`, `OAI.CWEquivariant.toWhole`, `OAI.FiniteIndexProducts.homologyIso`, `OAI.FiniteIndexRegular.embed`, `OAI.FiniteIndexRegular.eval`, `OAI.FiniteIndexRegular.indIso`, `OAI.FiniteIndexRegular.invLM`, `OAI.HurewiczNormalized.differenceMap`, `OAI.HurewiczNormalized.toCycles`, `OAI.HurewiczNormalized.toHomology`, `OAI.PresentationGeometry.AttachingLoops.relatorSection`, `OAI.PresentationGeometry.FiniteStage.Attachment`, `OAI.PresentationGeometry.FiniteStage.Attachment.base`, `OAI.PresentationGeometry.FiniteStage.algebraicBeginning`, `OAI.PresentationGeometry.FiniteStage.attachment`, `OAI.PresentationGeometry.FiniteStage.attachments`, `OAI.PresentationGeometry.FiniteStage.cellStep`, `OAI.PresentationGeometry.FiniteStage.finalCW`, `OAI.PresentationGeometry.FiniteStage.finalSpace`, `OAI.PresentationGeometry.FiniteStage.indexStep`, `OAI.PresentationGeometry.FiniteStage.next`, `OAI.PresentationGeometry.FiniteStage.sphereFamily`, `OAI.PresentationGeometry.FiniteStage.stageCell`, `OAI.PresentationGeometry.FiniteStage.stageI`, `OAI.PresentationGeometry.FiniteStage.stageIndex`, `OAI.PresentationGeometry.FiniteStage.stageMap`, `OAI.PresentationGeometry.FiniteStage.stageX`, `OAI.PresentationGeometry.FiniteStage.stages`, `OAI.PresentationGeometry.FiniteStage.step`, `OAI.PresentationGeometry.FiniteStage.succCell`, `OAI.PresentationGeometry.FiniteStage.succIndex`, `OAI.PresentationGeometry.FiniteStage.succMap`, `OAI.PresentationGeometry.PresentationComplex.coveringCore` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_BasedHorn`, `FiniteType_CoreDeck`, `FiniteType_CoreDeckLeftQuotientCovering`, `FiniteType_CoveringCellGeometryHausdorff`, `FiniteType_FiniteIndexProducts`, `FiniteType_FiniteIndexRegular`, `FiniteType_HurewiczInverse`, `FiniteType_PartialResolutionPartialCyclesFg`, `FiniteType_PresentationGeometryCells`, `FiniteType_PresentationGeometryFiniteStage`, `FiniteType_PresentationGeometryRose`, `FiniteType_PresentationVanKampenRectanglePaths`, `FiniteType_ProductFiniteResolutionBeginningOfComplex`, `FiniteType_RegularCoverGeometry`, `FiniteType_SingularAction`, `FiniteType_SingularChains`, `FiniteType_SingularPrism`, `FiniteType_SingularSigmaSingleMerge`, `FiniteType_SingularSphereCycle`, `FiniteType_TwistedBrin`.
--
--   **Imports.** It imports the bundles `OAIQ66So023`, `OAIQ66So024`, `OAIQ66So025` and `OAIQ66So026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So030` and `OAIQ66So031`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So023
import Definitions.Def_OAIQ66So024
import Definitions.Def_OAIQ66So025
import Definitions.Def_OAIQ66So026

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCells
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.Rose.disk_contractible _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
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
section
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

theorem old_fundamentalGroupMap_surjective (hd : 1 < d) (b : X) :
    Function.Surjective (FundamentalGroup.map
      (⟨Adjunction.old f, Adjunction.continuous_old f⟩ : C(X, Space f)) b) := by
  let bU : collar f := ⟨Adjunction.old f b, mem_collar_old f b⟩
  let r : C(collar f, X) := (shellRetraction f).comp (collarToShell f)
  have hr : r bU = b := by simp [r, bU]
  intro g
  obtain ⟨gU, hgU⟩ := collar_fundamentalGroupMap_surjective f hd bU g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective gU
  let q : Path b b := (p.map r.continuous).cast hr.symm hr.symm
  refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
  rw [← hgU]
  change Path.Homotopic.Quotient.mk (q.map (Adjunction.continuous_old f)) =
    Path.Homotopic.Quotient.mk (p.map continuous_subtype_val)
  apply Quotient.sound
  apply Path.Homotopic.symm
  refine ⟨{
    toFun := fun z => shellSlide f z.1 (collarToShell f (p z.2))
    continuous_toFun := (shellSlide_continuous f).comp
      (continuous_fst.prodMk ((collarToShell f).continuous.comp
        (p.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    simp only [shellSlide_zero, shellInclude_collarToShell, Path.coe_toContinuousMap,
      Path.map_coe, Function.comp_apply]
  · intro t
    change shellSlide f 1 (collarToShell f (p t)) = Adjunction.old f (r (p t))
    exact shellSlide_one f _
  · intro t s hs
    rcases hs with hs | hs
    · subst s
      change shellSlide f t (collarToShell f (p 0)) = (p 0 : Space f)
      rw [p.source]
      simp [bU]
    · have hs' : s = 1 := hs
      subst s
      change shellSlide f t (collarToShell f (p 1)) = (p 1 : Space f)
      rw [p.target]
      simp [bU]

end

open Set Metric

end PresentationGeometry.Cells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RegularCoverGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.Rose.disk_contractible _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
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

theorem coveringCore_simplyConnected [SimplyConnectedSpace Z.TotalSpace] (hd : 1 < d) :
    SimplyConnectedSpace (coveringCore f b Z pot s hs hpot).TotalSpace := by
  let : PathConnectedSpace X := (show Function.Surjective Z.proj from
    fun x => ⟨⟨x,(1 : Q)⟩,rfl⟩).pathConnectedSpace Z.continuous_proj
  let : PathConnectedSpace (Cells.Space f) := Cells.pathConnectedSpace f (by omega)
  exact CoveringMapNatural.simplyConnected_of_old (FiberBundle.isCoveringMap (F := Q) (E := Z.Fiber))
    (coveringCore_isCoveringMap f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ (oldLift f b Z pot s hs hpot)
    (funext (oldLift_proj f b Z pot s hs hpot)) ⟨b,(1 : Q)⟩
    (old_fundamentalGroupMap_surjective f hd b)
    (oldLift_fiber_bijective f b Z pot s hs hpot b)

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometryHausdorff
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.Rose.disk_contractible _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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

lemma oldLift_homology_surjective (j : ℕ) (hj : j < d) :
    Function.Surjective (homologyMap (map (oldLift f b Z pot s hs hpot)) j) := by
  let := Cells.cwComplex f hdim
  let := CoveringCellGeometry.hausdorff (coveringCore_isCoveringMap f b Z pot s hs hpot)
  let := CoveringCW.cwComplex_general (coveringCore_isCoveringMap f b Z pot s hs hpot)
  exact CWCellular.homology_skeleton_surjective (oldLift f b Z pot s hs hpot)
    (oldLift_isEmbedding f b Z pot s hs hpot) d (oldLift_skeleton f b Z pot s hs hpot hdim) j hj

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularPrism
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits

namespace SingularChains
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma prism_precomp (F : C(I × X,Y)) (p : C(Z,X)) (n : ℕ) :
    prism (precompCylinder F p) n = (map p).f n ≫ prism F n := by
  exact SingularPrism.prism_precomp (f := TopCat.ofHom (start F)) (g := TopCat.ofHom (finish F))
    (cylinderHom F) (TopCat.ofHom p) n

lemma prism_boundary_zero (F : C(I × X,Y)) :
    (map (start F)).f 0 = prism F 0 ≫ (chains Y).d 1 0 + (map (finish F)).f 0 := by
  have h := (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).comm 0
  rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,zero_add] at h
  exact h

lemma prism_boundary_succ (F : C(I × X,Y)) (n : ℕ) :
    (map (start F)).f (n+1) =
      (chains X).d (n+1) n ≫ prism F n +
        prism F (n+1) ≫ (chains Y).d (n+2) (n+1) + (map (finish F)).f (n+1) := by
  have h := (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).comm (n+1)
  rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex] at h
  exact h

end SingularChains

namespace SingularNormalization
section
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval
open SingularChains
variable {X : Type} [TopologicalSpace X]

namespace Coherent
variable (S : Coherent X)

lemma top_comm (n : ℕ) :
    S.topComponent (n+1) ≫ (chains X).d (n+1) n =
      (chains X).d (n+1) n ≫ S.topComponent n := by
  apply hom_ext
  intro f
  simp only [topComponent,← Category.assoc,generator_boundary,
    Preadditive.sum_comp,Preadditive.zsmul_comp,generator_desc]
  simp only [top_face]

def topMap : chains X ⟶ chains X where
  f := S.topComponent
  comm' i j hij := by
    have he : j+1 = i := hij
    subst i
    exact S.top_comm j

def prismComponent (n : ℕ) : (chains X).X n ⟶ (chains X).X (n+1) :=
  desc (fun f => generator (ContinuousMap.id (Std n)) ≫ prism (S.H n f) n)

lemma identity_prism_zero (f : C(Std 0,X)) :
    generator f =
      generator (ContinuousMap.id (Std 0)) ≫ prism (S.H 0 f) 0 ≫ (chains X).d 1 0 +
      generator (S.top 0 f) := by
  have h := congrArg (fun a => generator (ContinuousMap.id (Std 0)) ≫ a)
    (prism_boundary_zero (S.H 0 f))
  simpa only [Preadditive.comp_add,generator_map,start_eq,ContinuousMap.comp_id,
    Category.assoc,top] using h

lemma lifted_face_prism (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    generator (SingularChains.face i) ≫ prism (S.H (n+1) f) n =
      generator (ContinuousMap.id (Std n)) ≫ prism (S.H n (f.comp (SingularChains.face i))) n := by
  rw [← S.hom_face,prism_precomp,← Category.assoc,generator_map,ContinuousMap.comp_id]

lemma identity_prism_succ (n : ℕ) (f : C(Std (n+1),X)) :
    generator f =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (generator (ContinuousMap.id (Std n)) ≫ prism (S.H n (f.comp (SingularChains.face i))) n)) +
      generator (ContinuousMap.id (Std (n+1))) ≫
        prism (S.H (n+1) f) (n+1) ≫ (chains X).d (n+2) (n+1) +
      generator (S.top (n+1) f) := by
  have h := congrArg (fun a => generator (ContinuousMap.id (Std (n+1))) ≫ a)
    (prism_boundary_succ (S.H (n+1) f) n)
  simp only [Preadditive.comp_add,generator_map,start_eq,ContinuousMap.comp_id,
    ← Category.assoc,generator_boundary,Preadditive.sum_comp,Preadditive.zsmul_comp,
    ContinuousMap.id_comp,S.lifted_face_prism] at h
  exact h

lemma prism_comm_zero :
    𝟙 ((chains X).X 0) = S.prismComponent 0 ≫ (chains X).d 1 0 + S.topComponent 0 := by
  apply hom_ext
  intro f
  simpa only [Category.comp_id,Preadditive.comp_add,prismComponent,topComponent,
    generator_desc_assoc,generator_desc,Category.assoc] using S.identity_prism_zero f

lemma prism_comm_succ (n : ℕ) :
    𝟙 ((chains X).X (n+1)) = (chains X).d (n+1) n ≫ S.prismComponent n +
      S.prismComponent (n+1) ≫ (chains X).d (n+2) (n+1) + S.topComponent (n+1) := by
  apply hom_ext
  intro f
  simpa only [Category.comp_id,Preadditive.comp_add,prismComponent,topComponent,
    generator_desc_assoc,generator_desc,← Category.assoc,generator_boundary,
    Preadditive.sum_comp,Preadditive.zsmul_comp,generator_desc] using S.identity_prism_succ n f

def homComponent (n m : ℕ) : (chains X).X n ⟶ (chains X).X m :=
  if h : n+1 = m then S.prismComponent n ≫ eqToHom (congrArg (chains X).X h) else 0

lemma homComponent_succ (n : ℕ) : S.homComponent n (n+1) = S.prismComponent n := by
  simp [homComponent]

def chainHomotopy : Homotopy (𝟙 (chains X)) S.topMap where
  hom := S.homComponent
  zero i j h := by simp only [ComplexShape.down_Rel] at h; simp [homComponent,h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,zero_add,
        homComponent_succ]
      exact S.prism_comm_zero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,
        homComponent_succ,homComponent_succ]
      exact S.prism_comm_succ n

end Coherent

open Coherent

end

open _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains

end SingularNormalization

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval

namespace HurewiczNormalized

open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X : Type} [TopologicalSpace X] {k : ℕ}
variable (hπ : ∀ p < k+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x₀ : X)

def differenceMap : chains X ⟶ chains X :=
  (SingularNormalization.tightening hπ x₀).topMap - map (ContinuousMap.const X x₀)

lemma difference_generator (f : C(Std (k+1),X)) :
    generator f ≫ (differenceMap hπ x₀).f (k+1) = cycle (normalizedSimplex hπ x₀ f) := by
  simp only [differenceMap,sub_f_apply,Preadditive.comp_sub]
  change generator f ≫ desc _ - _ = _
  rw [generator_desc,generator_map]
  rfl

lemma difference_cycle :
    (differenceMap hπ x₀).f (k+1) ≫ (chains X).d (k+1) k = 0 := by
  apply SingularChains.hom_ext
  intro f
  rw [← Category.assoc,difference_generator,comp_zero]
  have h := cycle_d (normalizedSimplex hπ x₀ f)
  rw [Nat.add_sub_cancel] at h
  exact h

def toCycles : (chains X).X (k+1) ⟶ (chains X).cycles (k+1) :=
  (chains X).liftCycles ((differenceMap hπ x₀).f (k+1)) k
    (by simp [ChainComplex.next_nat_succ]) (difference_cycle hπ x₀)

def toHomology : (chains X).X (k+1) ⟶ (chains X).homology (k+1) :=
  toCycles hπ x₀ ≫ (chains X).homologyπ (k+1)

lemma difference_homology : homologyMap (differenceMap hπ x₀) (k+1) = 𝟙 _ := by
  rw [differenceMap,homologyMap_sub]
  have he := (SingularNormalization.tightening hπ x₀).chainHomotopy.homologyMap_eq (k+1)
  rw [homologyMap_id] at he
  rw [← he,SingularNormalization.homologyMap_const (k+1) (by omega) x₀,sub_zero]

lemma cycles_toHomology :
    (chains X).iCycles (k+1) ≫ toHomology hπ x₀ = (chains X).homologyπ (k+1) := by
  have he : (chains X).iCycles (k+1) ≫ toCycles hπ x₀ =
      cyclesMap (differenceMap hπ x₀) (k+1) := by
    apply (cancel_mono ((chains X).iCycles (k+1))).1
    simp only [Category.assoc,toCycles,liftCycles_i,cyclesMap_i]
  rw [toHomology,← Category.assoc,he,← homologyπ_naturality,difference_homology,Category.comp_id]

instance toHomology_epi : Epi (toHomology hπ x₀) :=
  epi_of_epi_fac (cycles_toHomology hπ x₀)

lemma generator_toHomology (f : C(Std (k+1),X)) :
    generator f ≫ toHomology hπ x₀ =
      cycleClassHom (cycle (normalizedSimplex hπ x₀ f)) (cycle_d _) := by
  simp only [toHomology,← Category.assoc,toCycles,comp_liftCycles,difference_generator]
  rfl

include hπ in

theorem canonical_span :
    Submodule.span ℤ (Set.range (HurewiczConstruction.canonical (k+1) (X := X) (x := x₀))) = ⊤ := by
  let P := Submodule.span ℤ
    (Set.range (HurewiczConstruction.canonical (k+1) (X := X) (x := x₀)))
  let : Module ℤ ((chains X).homology (k+1) ⧸ P) := Submodule.Quotient.module P
  let q : (chains X).homology (k+1) ⟶ ModuleCat.of ℤ ((chains X).homology (k+1) ⧸ P) :=
    ModuleCat.ofHom P.mkQ
  have hq : toHomology hπ x₀ ≫ q = 0 := by
    apply SingularChains.hom_ext
    intro f
    rw [← Category.assoc,generator_toHomology,comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change P.mkQ (homologyClass (normalizedSimplex hπ x₀ f)) = 0
    change homologyClass (normalizedSimplex hπ x₀ f) ∈ LinearMap.ker P.mkQ
    rw [Submodule.ker_mkQ]
    rw [← canonical_simplex]
    exact Submodule.subset_span ⟨_,rfl⟩
  have hqzero : q = 0 := (cancel_epi (toHomology hπ x₀)).mp (by simpa using hq)
  apply top_unique
  intro z _
  have hz := congrArg (fun t => t z) hqzero
  change P.mkQ z = 0 at hz
  have hz' : z ∈ LinearMap.ker P.mkQ := hz
  simpa only [Submodule.ker_mkQ] using hz'

end HurewiczNormalized

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedHorn
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace DuffyHurewicz
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains HurewiczNormalized DuffyBased
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

theorem surjective
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    Function.Surjective (hom n x) := by
  let P : Submodule ℤ ((chains X).homology (n+1)) :=
    { (hom n x).range with
      smul_mem' := fun c y hy => by
        change ((chains X).homology (n+1)).isModule.smul c y ∈ (hom n x).range
        rw [int_smul_eq_zsmul]
        exact AddSubgroup.zsmul_mem (hom n x).range hy c }
  have hP : Submodule.span ℤ (Set.range (HurewiczConstruction.canonical (n+1) (X:=X) (x:=x))) ≤ P :=
    Submodule.span_le.mpr (range_canonical_le_range x)
  rw [HurewiczNormalized.canonical_span hπ x] at hP
  intro z
  exact hP (Submodule.mem_top) 

end DuffyHurewicz

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HurewiczInverse
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace HurewiczConstruction
section
open SingularChains SphereQuotient _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] {n : ℕ}

theorem exists_sphere
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)
    (z : (chains X).homology (n+1)) :
    ∃ f : C(Boundary (n+2),X),
      pushforward (n+1) f (SingularSphereCycle.fundamentalClass (n+1)) = z := by
  obtain ⟨p,hp⟩ := DuffyHurewicz.surjective hπ x z
  change DuffyHurewicz.value p.toMul = z at hp
  have hr : ∀ q : HomotopyGroup.Pi (n+1) X x,
      ∃ f : C(Boundary (n+2),X),
        pushforward (n+1) f (SingularSphereCycle.fundamentalClass (n+1)) =
          DuffyHurewicz.value q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      let s := DuffyBased.ofLoop a
      refine ⟨sphereMap (BasedSimplex.loop s),?_⟩
      change canonical (n+1) (BasedSimplex.homotopyClass s) = _
      rw [HurewiczNormalized.canonical_simplex]
      rfl
  obtain ⟨f,hf⟩ := hr p.toMul
  exact ⟨f,hf.trans hp⟩

variable {G : Type} [Group G] [MulAction G X] [ContinuousConstSMul G X]

theorem finite_sphere_generators
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)
    [Module.Finite (MonoidAlgebra ℤ G) (homologyModule (G:=G) (X:=X) (n+1))] :
    ∃ (k : ℕ) (s : Fin k → C(Boundary (n+2),X)),
      Submodule.span (MonoidAlgebra ℤ G)
        (Set.range (fun i => sphereModuleClass (G:=G) (n+1) (s i))) = ⊤ := by
  obtain ⟨k,z,hz⟩ := Module.Finite.exists_fin (R:=MonoidAlgebra ℤ G)
    (M:=homologyModule (G:=G) (X:=X) (n+1))
  choose s hs using fun i => exists_sphere hπ x (z i)
  refine ⟨k,s,?_⟩
  have he : (fun i => sphereModuleClass (G:=G) (n+1) (s i)) = z :=
    funext hs
  rw [he]
  exact hz
end

open CategoryTheory.Limits SingularChains
variable {X : Type} [TopologicalSpace X]

theorem homotopy_trivial_of_homology_zero [SimplyConnectedSpace X] (n : ℕ)
    (hH : ∀ j, 2 ≤ j → j ≤ n → IsZero ((chains X).homology j)) :
    ∀ j ≤ n, ∀ x : X, Subsingleton (HomotopyGroup (Fin j) X x) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj x
    cases j with
    | zero => exact homotopy_zero x
    | succ j =>
      cases j with
      | zero => exact homotopy_one x
      | succ j =>
        have hp : ∀ p < j+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z) :=
          fun p h z => ih p h (by omega) z
        let := (ModuleCat.isZero_iff_subsingleton.mp (hH (j+2) (by omega) hj))
        have hi := DuffyHurewicz.injective hp x
        exact (hi.comp (show Function.Injective (Additive.ofMul :
          HomotopyGroup.Pi (j+2) X x → Additive (HomotopyGroup.Pi (j+2) X x)) from fun _ _ h => h)).subsingleton

lemma homology_zero_of_homotopy {n : ℕ}
    (hπ : ∀ p ≤ n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    IsZero ((chains X).homology (n+1)) := by
  let := hπ (n+1) le_rfl x
  have hs := DuffyHurewicz.surjective (n:=n) (fun p h z => hπ p (by omega) z) x
  let : Subsingleton ((chains X).homology (n+1)) := hs.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end HurewiczConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigmaSingleMerge
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SingularChains.zeroAugmentation_isIso _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

lemma oriented_boundary (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1))) :
    (orientedIso n).hom (boundary n x) = d n ((orientedIso (n+1)).hom x) := by
  change ((orientedIso n).inv ≫ (orientedIso n).hom) (d n ((orientedIso (n+1)).hom x)) = _
  rw [Iso.inv_hom_id]
  rfl

include hc in
lemma boundary_smul (g : G) (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1))) :
    boundary n (rep (G := G) (n+1) g x) = rep (G := G) n g (boundary n x) := by
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom _ = (orientedIso n).hom _
  rw [oriented_boundary,← orientedIso_smul hc,← orientedIso_smul hc,oriented_boundary]
  exact (congrArg (fun k => k ((orientedIso (n+1)).hom x)) ((skeletal hc g).d_natural n)).symm

def boundaryIntertwiner (n : ℕ) : (rep (G := G) (X := X) (n+1)).IntertwiningMap (rep (G := G) (X := X) n) :=
  (boundary n).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => boundary_smul hc g n x)

def moduleBoundary (n : ℕ) : module (G := G) (X := X) (n+1) →ₗ[MonoidAlgebra ℤ G] module (G := G) (X := X) n :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ (boundaryIntertwiner hc n)

lemma boundary_comp (n : ℕ) : (moduleBoundary hc n).comp (moduleBoundary hc (n+1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom (boundary n (boundary (n+1) x)) = (orientedIso n).hom 0
  erw [map_zero,oriented_boundary,oriented_boundary]
  exact congrArg (fun f => f ((orientedIso (n+2)).hom x)) (d_comp_d (C := (univ : Set X)) n)

lemma boundary_exact (n : ℕ) (h : Limits.IsZero ((SingularChains.chains (univ : Set X)).homology (n+1))) :
    Function.Exact (moduleBoundary hc (n+1)) (moduleBoundary hc n) := by
  intro x
  constructor
  · intro hx
    have hx' : d n ((orientedIso (n+1)).hom x) = 0 := by
      erw [← oriented_boundary]
      change (orientedIso n).hom (moduleBoundary hc n x) = 0
      erw [hx,map_zero]
    obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_of_homology_zero n h)
      ((orientedIso (n+1)).hom x) hx'
    refine ⟨(orientedIso (n+2)).inv y,?_⟩
    apply (orientedIso (n+1)).toLinearEquiv.injective
    change (orientedIso (n+1)).hom (boundary (n+1) ((orientedIso (n+2)).inv y)) = _
    rw [oriented_boundary]
    change CWCellular.d (n+1) (((orientedIso (n+2)).inv ≫ (orientedIso (n+2)).hom) y) = _
    rw [Iso.inv_hom_id]
    exact hy
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (boundary_comp hc n)

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def differential (n : ℕ) : object (G:=G) (X:=X) (n+1) ⟶ object (G:=G) (X:=X) n :=
  Rep.ofHom (boundaryIntertwiner hc n)
lemma differential_comp (n : ℕ) : differential hc (n+1) ≫ differential hc n = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun f => f x) (boundary_comp hc n)

def complex : ChainComplex (Rep ℤ G) ℕ :=
  ChainComplex.of (object (G:=G) (X:=X)) (differential hc) (differential_comp hc)

lemma complex_exactAt (n : ℕ)
    (hz : CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology (n+1))) :
    (complex hc).ExactAt (n+1) := by
  rw [exactAt_iff' _ (n+2) (n+1) n
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl)]
  change (ShortComplex.mk ((complex hc).d (n+2) (n+1)) ((complex hc).d (n+1) n) _).Exact
  have hd₁ : (complex hc).d (n+2) (n+1) = differential hc (n+1) := ChainComplex.of_d _ _ _
  have hd₂ : (complex hc).d (n+1) n = differential hc n := ChainComplex.of_d _ _ _
  simp only [hd₁,hd₂]
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact (boundary_exact hc n hz x).mp hx

lemma d_aug : (complex hc).d 1 0 ≫ aug hc = 0 := by
  ext x
  change (augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
      ((orientedIso 0).hom (boundary 0 x)) = 0
  erw [oriented_boundary]
  change (CWCellular.d 0 ≫ augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    ((orientedIso 1).hom x) = 0
  rw [← Category.assoc,d_augmentation,CategoryTheory.Limits.zero_comp]
  rfl

lemma aug_exact [PathConnectedSpace (univ : Set X)] :
    (ShortComplex.mk ((complex hc).d 1 0) (aug hc) (d_aug hc)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : augmentation ((orientedIso 0).hom x) = 0 := by
    apply (ModuleCat.mono_iff_injective (SingularChains.zeroAugmentation (univ : Set X))).mp inferInstance
    rw [map_zero]
    exact hx
  obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (augmentation_exact (C:=(univ : Set X))) _ hx'
  refine ⟨(orientedIso 1).inv y,?_⟩
  apply (orientedIso 0).toLinearEquiv.injective
  change (orientedIso 0).hom (boundary 0 ((orientedIso 1).inv y)) = _
  rw [oriented_boundary]
  change CWCellular.d 0 (((orientedIso 1).inv ≫ (orientedIso 1).hom) y) = _
  rw [Iso.inv_hom_id]
  exact hy

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PartialResolutionPartialCyclesFg
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWEquivariant
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

lemma cycles_fg [PathConnectedSpace (univ : Set X)] [∀ i, Projective (object (G:=G) (X:=X) i)]
    (n : ℕ) {α β : Type} [Finite α]
    (eC : object (G:=G) (X:=X) (n+1) ≅ Rep.free ℤ G α)
    (eD : object (G:=G) (X:=X) n ≅ Rep.free ℤ G β)
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    (moduleBoundary hc n).ker.FG := by
  let : Epi (show (complex hc).X 0 ⟶ Rep.trivial ℤ G ℤ from aug hc) := aug_epi hc
  have : ∀ i, Projective ((complex hc).X i) := fun i => inferInstanceAs (Projective (object i))
  have h := PartialResolution.partial_cycles_fg (complex hc) (n+1) (by omega) (aug hc)
    (d_aug hc) (aug_exact hc) (fun i hi h => by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact complex_exactAt hc j (hex (j+1) hi h)) eC (by simpa only [Nat.add_sub_cancel_right,complex,ChainComplex.of_X] using eD) hzero
  rw [show (n+1)-1=n by omega] at h
  have hd : (complex hc).d (n+1) n = differential hc n := ChainComplex.of_d _ _ _
  rw [hd] at h
  exact h

def qLinear (n : ℕ) : ((absoluteRep hc (n+1) n) : Type) →ₗ[ℤ]
    MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n) :=
  (q n n ≫ (orientedIso n).inv).hom

lemma qLinear_smul (g : G) (n : ℕ) (x : absoluteRep hc (n+1) n) :
    qLinear hc n ((absoluteRep hc (n+1) n).ρ g x) = rep (G:=G) n g (qLinear hc n x) := by
  apply (orientedIso n).toLinearEquiv.injective
  change ((q n n ≫ (orientedIso n).inv) ≫ (orientedIso n).hom)
    ((homologyMap ((skeletal hc g).absoluteMap (n+1)) n) x) = _
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change q n n ((homologyMap ((skeletal hc g).absoluteMap (n+1)) n) x) =
    (orientedIso n).hom (rep (G:=G) n g (qLinear hc n x))
  rw [← orientedIso_smul hc]
  change (homologyMap ((skeletal hc g).absoluteMap (n+1)) n ≫ q n n) x =
    ((q n n ≫ (orientedIso n).inv ≫ (orientedIso n).hom) ≫ (skeletal hc g).cellMap n) x
  rw [Iso.inv_hom_id,Category.comp_id,← (skeletal hc g).q_natural]
  rfl

def qRep (n : ℕ) : absoluteRep hc (n+1) n ⟶ object (G:=G) (X:=X) n :=
  Rep.ofHom ((qLinear hc n).intertwiningMap_of_isIntertwiningMap _ _
    (fun g x => qLinear_smul hc g n x))

lemma qRep_boundary (n : ℕ) : qRep hc (n+1) ≫ differential hc n = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom (boundary n ((orientedIso (n+1)).inv (q (n+1) (n+1) x))) =
    (orientedIso n).hom 0
  rw [map_zero,oriented_boundary]
  change CWCellular.d n (((orientedIso (n+1)).inv ≫ (orientedIso (n+1)).hom) (q (n+1) (n+1) x)) = 0
  rw [Iso.inv_hom_id]
  exact congrArg (fun f => f x) (q_d (C:=(univ : Set X)) n)

def cyclesMap (n : ℕ) : (absoluteRep hc (n+2) (n+1)).ρ.asModule →ₗ[MonoidAlgebra ℤ G]
    (moduleBoundary hc n).ker :=
  (moduleMap (qRep hc (n+1))).codRestrict _ (fun x => by
    exact congrArg (fun f => moduleMap f x) (qRep_boundary hc n))

lemma cyclesMap_bijective (n : ℕ) : Function.Bijective (cyclesMap hc n) := by
  constructor
  · intro x y h
    apply top_injective (C:=(univ : Set X)) (n+1)
    have h' := congrArg (fun z => (orientedIso (n+1)).hom z) (congrArg Subtype.val h)
    change ((q (n+1) (n+1) ≫ (orientedIso (n+1)).inv) ≫ (orientedIso (n+1)).hom) x =
      ((q (n+1) (n+1) ≫ (orientedIso (n+1)).inv) ≫ (orientedIso (n+1)).hom) y at h'
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using h'
  · intro z
    have hz : CWCellular.d n ((orientedIso (n+1)).hom z.1) = 0 := by
      erw [← oriented_boundary]
      change (orientedIso n).hom (moduleBoundary hc n z.1) = 0
      erw [z.2,map_zero]
    obtain ⟨x,hx⟩ := (top_image (C:=(univ : Set X)) n _).mp hz
    refine ⟨x,Subtype.ext ?_⟩
    change (orientedIso (n+1)).inv (q (n+1) (n+1) x) = z.1
    rw [hx]
    exact congrArg (fun f => f z.1) (orientedIso (n+1)).hom_inv_id

def cyclesEquiv (n : ℕ) : (absoluteRep hc (n+2) (n+1)).ρ.asModule ≃ₗ[MonoidAlgebra ℤ G]
    (moduleBoundary hc n).ker := LinearEquiv.ofBijective (cyclesMap hc n) (cyclesMap_bijective hc n)

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def toWhole (m j : ℕ) : absoluteRep hc m j ⟶ wholeRep (G:=G) (X:=X) j :=
  Rep.ofHom ((homologyMap (SingularChains.map (skelToComplex (C:=(univ : Set X)) m)) j).hom.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change ((homologyMap ((skeletal hc g).absoluteMap m) j ≫
      homologyMap (SingularChains.map (skelToComplex m)) j) x) =
      ((homologyMap (SingularChains.map (skelToComplex m)) j ≫
        homologyMap (SingularChains.map (onSpace g)) j) x)
    rw [← homologyMap_comp,← homologyMap_comp]
    congr 1
    unfold SkeletalMap.absoluteMap
    rw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl))

lemma toWhole_surjective (m j : ℕ) (hj : j < m) :
    Function.Surjective (moduleMap (toWhole hc m j)) :=
  homology_toComplex_surjective_top m j hj

include hc in

lemma homology_finite [PathConnectedSpace (univ : Set X)]
    [∀ i, Projective (object (G:=G) (X:=X) i)]
    (n : ℕ) {α β : Type} [Finite α]
    (eC : object (G:=G) (X:=X) (n+1) ≅ Rep.free ℤ G α)
    (eD : object (G:=G) (X:=X) n ≅ Rep.free ℤ G β)
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    Module.Finite (MonoidAlgebra ℤ G) (wholeRep (G:=G) (X:=X) (n+1)).ρ.asModule := by
  have : Module.Finite (MonoidAlgebra ℤ G) (moduleBoundary hc n).ker :=
    Module.Finite.of_fg (cycles_fg hc n eC eD hex hzero)
  have : Module.Finite (MonoidAlgebra ℤ G) (absoluteRep hc (n+2) (n+1)).ρ.asModule :=
    Module.Finite.equiv (cyclesEquiv hc n).symm
  exact Module.Finite.of_surjective (moduleMap (toWhole hc (n+2) (n+1)))
    (toWhole_surjective hc _ _ (by omega))

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
namespace SingularAction
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end SingularAction

end

namespace EquivariantCoverCells
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CWEquivariant CWExtension CoveringCW
variable {X E G : Type} [TopologicalSpace X] [TopologicalSpace E]
  [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
  [Group G] [MulAction G E] [ContinuousConstSMul G E]
  {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
  (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
  (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
  (surj : Function.Surjective p) (cov : IsCoveringMap p)

include hfree htrans surj cov in

lemma homology_finite [PathConnectedSpace (univ : Set E)]
    (n : ℕ) [Finite (RelCWComplex.cell (univ : Set X) (n+1))]
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set E)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    Module.Finite (MonoidAlgebra ℤ G) (wholeRep (G:=G) (X:=E) (n+1)).ρ.asModule := by
  let := CoveringCW.cwComplex_general cov
  let : ∀ m, MulAction G (RelCWComplex.cell (univ : Set E) m) := fun m => cellAction (p:=p) m
  have hc : ∀ (g : G) m (i : RelCWComplex.cell (univ : Set E) m) (v : CWExtension.Disk m),
      g • RelCWComplex.map m i v = RelCWComplex.map m (g • i) v := chart_smul cov
  have e (m : ℕ) : object (G:=G) (X:=E) m ≅ Rep.free ℤ G (RelCWComplex.cell (univ : Set X) m) :=
    freeIso hfree htrans surj m
  let : ∀ m, Projective (object (G:=G) (X:=E) m) := fun m =>
    Projective.of_iso (e m).symm inferInstance
  exact CWEquivariant.homology_finite hc n (e (n+1)) (e n) hex hzero

attribute [instance] AddCommGroup.toIntModule
end EquivariantCoverCells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeck
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.CellCoverExtension
open Set Topology Cells CWExtension _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex SingularChains
open HurewiczConstruction
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k n : ℕ} (f : C(boundary k (n+3),X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k (n+3),Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)
  [Nonempty X] [CWComplex (univ : Set X)] [RelCWComplex.FiniteType (univ : Set X)]
  (hdim : ∀ m, RelCWComplex.cell (univ : Set X) m → m < n+3)

include hdim in

lemma critical_homology_zero_left
    (hgen : letI := CoreDeck.leftAction Z
      letI := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Q)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    IsZero ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
  let := CoreDeck.leftAction Z
  let := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
  have hzero : (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom = 0 := by
    apply RepresentationKilling.eq_zero (homologyRep (G:=Q) (X:=Z.TotalSpace) (n+2))
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom
      (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i))) hgen
    intro q i
    have hk := deck_attaching_homology_killed f b Z pot s hs hpot rfl i q⁻¹ (n+2) (by omega)
    exact congrArg (fun a => a (SingularSphereCycle.fundamentalClass (n+2))) hk
  have hsur := oldLift_homology_surjective f b Z pot s hs hpot hdim (n+2) (by omega)
  let : Subsingleton ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
    constructor
    intro u v
    obtain ⟨u,rfl⟩ := hsur u
    obtain ⟨v,rfl⟩ := hsur v
    change (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom u =
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom v
    rw [hzero]
    rfl
  exact ModuleCat.isZero_of_subsingleton _

include hdim in

theorem coveringCore_connectivity_left [SimplyConnectedSpace Z.TotalSpace]
    (hπ : ∀ p ≤ n+1, ∀ z : Z.TotalSpace, Subsingleton (HomotopyGroup (Fin p) Z.TotalSpace z))
    (hgen : letI := CoreDeck.leftAction Z
      letI := CoreDeck.continuousLeftAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Q)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    ∀ p ≤ n+2, ∀ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      Subsingleton (HomotopyGroup (Fin p) (coveringCore f b Z pot s hs hpot).TotalSpace z) := by
  let := coveringCore_simplyConnected f b Z pot s hs hpot (by omega)
  apply homotopy_trivial_of_homology_zero (n+2)
  intro j hj hjn
  by_cases he : j = n+2
  · subst j
    exact critical_homology_zero_left f b Z pot s hs hpot hdim hgen
  · have hj1 : j ≤ n+1 := by omega
    have hOld : IsZero ((chains Z.TotalSpace).homology j) := by
      cases j with
      | zero => omega
      | succ j => exact homology_zero_of_homotopy (fun p hp z => hπ p (hp.trans hj1) z) ⟨b,(1:Q)⟩
    let := ModuleCat.isZero_iff_subsingleton.mp hOld
    let := (oldLift_homology_surjective f b Z pot s hs hpot hdim j (by omega)).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
end PresentationGeometry.CellCoverExtension

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {ι X Q : Type} [TopologicalSpace X] [T2Space X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)
  [CWComplex (univ : Set X)] [SimplyConnectedSpace Z.TotalSpace]

lemma critical_finite (n : ℕ) [Finite (RelCWComplex.cell (univ : Set X) (n+2))]
    (hπ : ∀ p ≤ n+1, ∀ z : Z.TotalSpace,
      Subsingleton (HomotopyGroup (Fin p) Z.TotalSpace z))
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    letI := leftAction Z
    letI := continuousLeftAction Z hZ
    Module.Finite (MonoidAlgebra ℤ Q)
      (HurewiczConstruction.homologyModule (G:=Q) (X:=Z.TotalSpace) (n+2)) := by
  let := leftAction Z
  let := continuousLeftAction Z hZ
  let : T2Space Z.TotalSpace := CoveringCellGeometry.hausdorff (DiscreteCoverCharts.covering Z)
  let : Fact (∀ (g : Q) (x : Z.TotalSpace), Z.proj (g • x) = Z.proj x) := ⟨fun _ _ => rfl⟩
  let : PathConnectedSpace (univ : Set Z.TotalSpace) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_univ
  have hH (j : ℕ) (hj : 0 < j) (hjn : j < n+1+1) :
      IsZero ((SingularChains.chains (univ : Set Z.TotalSpace)).homology j) := by
    apply SingularAction.univ_homology_zero
    cases j with
    | zero => omega
    | succ j =>
      exact HurewiczConstruction.homology_zero_of_homotopy
        (fun p hp z => hπ p (by omega) z) (Classical.choice inferInstance)
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (CWEquivariant.wholeRep (G:=Q) (X:=Z.TotalSpace) (n+2)).ρ.asModule :=
    EquivariantCoverCells.homology_finite (left_free Z) (left_transitive Z)
      (fun x => ⟨⟨x,(1:Q)⟩,rfl⟩) (DiscreteCoverCharts.covering Z) (n+1) hH hzero
  exact SingularAction.finite_of_univ (G:=Q) (X:=Z.TotalSpace) (n+2)
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationVanKampenRectanglePaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.PresentationComplex
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

theorem freeToFundamental_surjective : Function.Surjective (freeToFundamental w) :=
  (Cells.old_fundamentalGroupMap_surjective (AttachingLoops.relators w)
    (by norm_num) (Rose.basepoint k)).comp (Rose.freeToFundamental_surjective k)

end PresentationGeometry.PresentationComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.AttachingLoops
open scoped unitInterval

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

def relatorSection : C(Cells.boundary r 2, (Rose.coveringCore g).TotalSpace) :=
  (liftedRelatorsOnCircle w g hw).comp boundaryCircle

@[simp] theorem relatorSection_proj (b : Cells.boundary r 2) :
    (Rose.coveringCore g).proj (relatorSection w g hw b) = relators w b := by
  exact onCircle_naturality (Rose.liftedRelator g (w b.1.1) (hw b.1.1))
    (Rose.wordLoop (w b.1.1)) ⟨_,(Rose.coveringCore g).continuous_proj⟩
    (Rose.liftedRelator_proj g (w b.1.1) (hw b.1.1)) _

end PresentationGeometry.AttachingLoops

namespace PresentationGeometry.PresentationComplex
section
open Set DiscreteCoverCharts
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

def coveringCore : FiberBundleCore (Option (Fin k) ⊕ Fin r) (Space w) Q :=
  CellCoverExtension.coveringCore (AttachingLoops.relators w) (Rose.basepoint k)
    (Rose.coveringCore g) (Rose.potential g) (AttachingLoops.relatorSection w g hw)
    (AttachingLoops.relatorSection_proj w g hw) (fun _ _ _ _ => rfl)

@[simp] theorem coveringCore_old_coordChange (i j : Option (Fin k)) (x : Rose.Space k) (q : Q) :
    (coveringCore w g hw).coordChange (.inl i) (.inl j) (includeRose w x) q =
      (Rose.coveringCore g).coordChange i j x q :=
  CellCoverExtension.coveringCore_old_coordChange ..

@[simp] theorem mem_coveringCore_old (i : Option (Fin k)) (x : Rose.Space k) :
    includeRose w x ∈ (coveringCore w g hw).baseSet (.inl i) ↔
      x ∈ (Rose.coveringCore g).baseSet i :=
  CellCoverExtension.mem_coveringCore_old ..

theorem basepoint_mem_coveringCore : basepoint w ∈ (coveringCore w g hw).baseSet (.inl none) :=
  (mem_coveringCore_old w g hw none (Rose.basepoint k)).mpr
    (Cells.mem_collar_old (Rose.attaching k) PUnit.unit)

theorem map_range_old_chart (i : Option (Fin k)) {a b : Rose.Space k} (p : Path a b)
    (hp : range p ⊆ (Rose.coveringCore g).baseSet i) :
    range (p.map (includeRose w).continuous) ⊆ (coveringCore w g hw).baseSet (.inl i) := by
  rintro _ ⟨t,rfl⟩
  exact (mem_coveringCore_old w g hw i (p t)).mpr (hp ⟨t,rfl⟩)

theorem monodromy_generator (i : Fin k) (q : Q) :
    (covering (coveringCore w g hw)).monodromy
      (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous))
      ⟨point (coveringCore w g hw) (.inl none) (basepoint w) q,rfl⟩ =
      ⟨point (coveringCore w g hw) (.inl none) (basepoint w) (g i * q),rfl⟩ := by
  let Z := coveringCore w g hw
  let p₁ := (Rose.edgeFirst i).map (includeRose w).continuous
  let p₂ := (Rose.edgeMiddle i).map (includeRose w).continuous
  let p₃ := (Rose.edgeLast i).map (includeRose w).continuous
  have hc₁ : range p₁ ⊆ Z.baseSet (.inl none) :=
    map_range_old_chart w g hw none _ (Rose.edgeFirst_collar i)
  have hc₂ : range p₂ ⊆ Z.baseSet (.inl (some i)) :=
    map_range_old_chart w g hw (some i) _ (Rose.edgeMiddle_interior i)
  have hc₃ : range p₃ ⊆ Z.baseSet (.inl none) :=
    map_range_old_chart w g hw none _ (Rose.edgeLast_collar i)
  have hn : point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q =
      point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q := by
    have h := point_change Z (.inl none) (.inl (some i))
      (hc₁ p₁.target_mem_range) (hc₂ p₂.source_mem_range) q
    simpa only [Z,coveringCore_old_coordChange,Rose.coveringCore,Rose.transition,
      Rose.potential_none,Rose.potential_negative,inv_one,one_mul] using h
  have hp : point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgePositive)) q =
      point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgePositive)) (g i * q) := by
    have h := point_change Z (.inl (some i)) (.inl none)
      (hc₂ p₂.target_mem_range) (hc₃ p₃.source_mem_range) q
    simpa only [Z,coveringCore_old_coordChange,Rose.coveringCore,Rose.transition,
      Rose.potential_none,Rose.potential_positive,inv_inv,one_mul] using h
  have he : Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous) =
      (Path.Homotopic.Quotient.mk p₁).trans
        ((Path.Homotopic.Quotient.mk p₂).trans (Path.Homotopic.Quotient.mk p₃)) := by
    simp only [← Path.Homotopic.Quotient.mk_trans]
    apply Quotient.sound
    change ((Rose.generatorLoop i).map (includeRose w).continuous).Homotopic (p₁.trans (p₂.trans p₃))
    have hh := (Rose.edge_parts_homotopic i).symm.map (includeRose w)
    simpa only [Path.map_trans] using hh
  erw [he,IsCoveringMap.monodromy_trans_apply,monodromy_chartPath Z (.inl none) _ hc₁]
  have hn' : (⟨point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q,rfl⟩ :
      Z.proj ⁻¹' {includeRose w (Rose.edgeMap i Rose.edgeNegative)}) =
      ⟨point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q,rfl⟩ := Subtype.ext hn
  erw [hn',IsCoveringMap.monodromy_trans_apply,monodromy_chartPath Z (.inl (some i)) _ hc₂]
  have hp' : (⟨point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgePositive)) q,rfl⟩ :
      Z.proj ⁻¹' {includeRose w (Rose.edgeMap i Rose.edgePositive)}) =
      ⟨point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgePositive)) (g i * q),rfl⟩ := Subtype.ext hp
  erw [hp',monodromy_chartPath Z (.inl none) _ hc₃]
  rfl

def monodromyRepresentation : FundamentalGroup (Space w) (basepoint w) →* Equiv.Perm Q :=
  ((fiberEquiv (coveringCore w g hw) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w g hw)).symm.permCongrHom.toMonoidHom).comp
      ((covering (coveringCore w g hw)).monodromyPerm (basepoint w))

@[simp] theorem monodromyRepresentation_generator (i : Fin k) (q : Q) :
    monodromyRepresentation w g hw (freeToFundamental w (FreeGroup.of i)) q = g i * q := by
  let e := fiberEquiv (coveringCore w g hw) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w g hw)
  have hg : Rose.freeToFundamental k (FreeGroup.of i) =
      (Path.Homotopic.Quotient.mk (Rose.generatorLoop i) :
        FundamentalGroup (Rose.Space k) (Rose.basepoint k)) := by
    exact FreeGroup.lift_apply_of (β := FundamentalGroup (Rose.Space k) (Rose.basepoint k))
      (f := fun i : Fin k => (Path.Homotopic.Quotient.mk (Rose.generatorLoop i) :
        FundamentalGroup (Rose.Space k) (Rose.basepoint k)))
  change monodromyRepresentation w g hw
    (FundamentalGroup.map (includeRose w) (Rose.basepoint k) (Rose.freeToFundamental k (FreeGroup.of i))) q = _
  rw [hg]
  change e.symm ((covering (coveringCore w g hw)).monodromy
    (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous)) (e q)) = _
  have h : (covering (coveringCore w g hw)).monodromy
      (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous)) (e q) = e (g i * q) :=
    monodromy_generator w g hw i q
  erw [h,e.symm_apply_apply]

end

open DiscreteCoverCharts

end PresentationGeometry.PresentationComplex

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
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

variable {Q} {n : ℕ} (S : Stage Q n)

def sphereFamily {k d : ℕ} {E : Type} [TopologicalSpace E]
    (s : Fin k → C(Boundary d,E)) : C(boundary k d,E) := by
  let t : C(Fin k × Boundary d,E) := ⟨fun z => s z.1 z.2,by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hf : ∀ᶠ w : Fin k × Boundary d in nhds z, w.1 = z.1 :=
      (continuous_fst.tendsto z).eventually (isOpen_discrete {z.1} |>.mem_nhds (by rfl))
    apply ((s z.1).continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [hf] with w hw
    simp only [hw,Function.comp_apply]⟩
  exact t.comp ⟨boundaryProductEquiv k d,(boundaryProductEquiv k d).continuous⟩

@[simp] lemma sphereFamily_slice {k d : ℕ} {E : Type} [TopologicalSpace E]
    (s : Fin k → C(Boundary d,E)) (i : Fin k) :
    (sphereFamily s).comp (boundarySlice i) = s i := rfl

structure Attachment where
  k : ℕ
  sphere : C(boundary k (n+3),S.core.TotalSpace)
  generates :
    letI := CoreDeck.leftAction S.core
    letI := CoreDeck.continuousLeftAction S.core (CoreDeck.of_potential S.core S.pot S.coord)
    Submodule.span (MonoidAlgebra ℤ Q)
      (Set.range (fun i : Fin k => sphereModuleClass (G:=Q) (n+2) (sphere.comp (boundarySlice i)))) = ⊤

lemma attachment_exists
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    Nonempty (Attachment S) := by
  let := CoreDeck.leftAction S.core
  let := CoreDeck.continuousLeftAction S.core (CoreDeck.of_potential S.core S.pot S.coord)
  let : Finite (RelCWComplex.cell (univ : Set S.X) (n+2)) :=
    RelCWComplex.FiniteType.finite_cell (n+2)
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (homologyModule (G:=Q) (X:=S.core.TotalSpace) (n+2)) :=
    CoreDeck.critical_finite S.core (CoreDeck.of_potential S.core S.pot S.coord) n S.connectivity hzero
  obtain ⟨k,s,hs⟩ := finite_sphere_generators (G:=Q) (n:=n+1)
    (fun p hp z => S.connectivity p (by omega) z) ⟨S.point,(1:Q)⟩
  exact ⟨⟨k,sphereFamily s,by simpa only [sphereFamily_slice] using hs⟩⟩

noncomputable def attachment
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep ℤ Q I) (n+2))) :
    Attachment S := Classical.choice (attachment_exists S hzero)

def Attachment.base (A : Attachment S) : C(boundary A.k (n+3),S.X) :=
  (⟨S.core.proj,S.core.continuous_proj⟩ : C(S.core.TotalSpace,S.X)).comp A.sphere

noncomputable def next (A : Attachment S) : Stage Q (n+1) where
  X := Cells.Space (A.base S)
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance
  cw := Cells.cwComplex (A.base S) S.dimension
  finite := Cells.cwComplex_finite (A.base S) S.dimension
  point := Adjunction.old (A.base S) S.point
  dimension := by
    intro m c
    change NewCell (X:=S.X) (k:=A.k) (d:=n+3) m at c
    rcases c with c | ⟨i,⟨h⟩⟩
    · have := S.dimension m c
      omega
    · omega
  I := S.I ⊕ Fin A.k
  core := coveringCore (A.base S) S.point S.core S.pot A.sphere (fun _ => rfl) S.coord
  pot := potential (A.base S) S.point S.core S.pot A.sphere
  coord := fun _ _ _ _ => rfl
  simply := coveringCore_simplyConnected (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord (by omega)
  connectivity := coveringCore_connectivity_left (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord S.dimension S.connectivity A.generates

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.FiniteStage

section
open Set Topology Metric Cells CWExtension CellCoverExtension
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {n : ℕ} (S : Stage Q n) (A : Attachment S)

def step : C(S.X,(next S A).X) := ⟨Adjunction.old (A.base S),Adjunction.continuous_old _⟩
lemma step_closed : IsClosedEmbedding (step S A) :=
  Adjunction.old_isClosedEmbedding (boundary_closed _ _) _
def cellStep (d : ℕ) : RelCWComplex.cell (univ : Set S.X) d ↪
    RelCWComplex.cell (univ : Set (next S A).X) d := ⟨Sum.inl,Sum.inl_injective⟩
lemma step_chart (d : ℕ) (c : RelCWComplex.cell (univ : Set S.X) d) (v : Fin d → ℝ) :
    step S A (RelCWComplex.map d c v) = RelCWComplex.map d (cellStep S A d c) v := rfl

def indexStep : S.I ↪ (next S A).I := ⟨Sum.inl,Sum.inl_injective⟩
lemma step_base (a : S.I) (x : S.X) :
    x ∈ S.core.baseSet a ↔ step S A x ∈ (next S A).core.baseSet (indexStep S A a) :=
  (mem_coveringCore_old (A.base S) S.point S.core S.pot A.sphere
    (fun _ => rfl) S.coord a x).symm
lemma step_pot (a : S.I) (x : S.X) :
    (next S A).pot (indexStep S A a) (step S A x) = S.pot a x := by
  change S.pot a (retractAt (A.base S) S.point (Adjunction.old (A.base S) x)) = _
  rw [retractAt_old]

variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))
noncomputable def stages : (n : ℕ) → Stage Q n
  | 0 => S₀
  | n+1 => next (stages n) (attachment (stages n) (fun I => hzero I (n+2) (by omega)))
noncomputable def attachments (n : ℕ) : Attachment (stages S₀ hzero n) :=
  attachment (stages S₀ hzero n) (fun I => hzero I (n+2) (by omega))
abbrev stageX (n : ℕ) := (stages S₀ hzero n).X
abbrev stageI (n : ℕ) := (stages S₀ hzero n).I
noncomputable def succMap (n : ℕ) : C(stageX S₀ hzero n,stageX S₀ hzero (n+1)) :=
  step _ (attachments S₀ hzero n)
noncomputable def succIndex (n : ℕ) : stageI S₀ hzero n ↪ stageI S₀ hzero (n+1) :=
  indexStep _ (attachments S₀ hzero n)
noncomputable def succCell (n d : ℕ) : RelCWComplex.cell (univ : Set (stageX S₀ hzero n)) d ↪
    RelCWComplex.cell (univ : Set (stageX S₀ hzero (n+1))) d :=
  cellStep _ (attachments S₀ hzero n) d
end

open Set Topology Metric
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))

noncomputable def stageMap (i j : ℕ) (h : i ≤ j) : C(stageX S₀ hzero i,stageX S₀ hzero j) :=
  ⟨Nat.leRecOn h (fun {k} x => succMap S₀ hzero k x),by
    induction j,h using Nat.le_induction with
    | base =>
      convert (continuous_id (X:=stageX S₀ hzero i)) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      exact Nat.leRecOn_self x
    | succ j h ih =>
      simpa only [Nat.leRecOn_succ h,Function.comp_def] using (succMap S₀ hzero j).continuous.comp ih⟩
instance mapSystem : DirectedSystem (stageX S₀ hzero) (stageMap S₀ hzero · · ·) where
  map_self {_} x := Nat.leRecOn_self x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
lemma stageMap_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (x : stageX S₀ hzero i) :
    stageMap S₀ hzero i (j+1) h' x = succMap S₀ hzero j (stageMap S₀ hzero i j h x) :=
  Nat.leRecOn_succ h x
lemma stageMap_closed (i j : ℕ) (h : i ≤ j) : IsClosedEmbedding (stageMap S₀ hzero i j h) := by
  induction j,h using Nat.le_induction with
  | base =>
    convert (IsClosedEmbedding.id (X:=stageX S₀ hzero i)) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact Nat.leRecOn_self x
  | succ j h ih =>
    have he : (stageMap S₀ hzero i (j+1) (by omega) : _) =
        (succMap S₀ hzero j).comp (stageMap S₀ hzero i j h) := by
      ext x; exact stageMap_succ S₀ hzero i j h _ x
    rw [he]
    exact (step_closed _ (attachments S₀ hzero j)).comp ih
noncomputable def stageIndex (i j : ℕ) (h : i ≤ j) : stageI S₀ hzero i ↪ stageI S₀ hzero j :=
  ⟨Nat.leRecOn h (fun {k} x => succIndex S₀ hzero k x),
    Nat.leRecOn_injective h _ (fun k => (succIndex S₀ hzero k).injective)⟩
instance indexSystem : DirectedSystem (stageI S₀ hzero) (stageIndex S₀ hzero · · ·) where
  map_self {_} x := Nat.leRecOn_self x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
lemma stageIndex_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (a : stageI S₀ hzero i) :
    stageIndex S₀ hzero i (j+1) h' a = succIndex S₀ hzero j (stageIndex S₀ hzero i j h a) :=
  Nat.leRecOn_succ h a
noncomputable def stageCell (i j : ℕ) (h : i ≤ j) (d : ℕ) :
    RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d ↪
    RelCWComplex.cell (univ : Set (stageX S₀ hzero j)) d :=
  ⟨Nat.leRecOn h (fun {k} x => succCell S₀ hzero k d x),
    Nat.leRecOn_injective h _ (fun k => (succCell S₀ hzero k d).injective)⟩
instance cellSystem (d : ℕ) : DirectedSystem
    (fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d)
    (fun i j h => stageCell S₀ hzero i j h d) where
  map_self {_} x := Nat.leRecOn_self (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) x
  map_map {_ _ _} h₁ h₂ x := (Nat.leRecOn_trans (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) h₁ h₂ x).symm
lemma stageCell_succ (i j : ℕ) (h : i ≤ j) (h' : i ≤ j+1) (d : ℕ)
    (c : RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) :
    stageCell S₀ hzero i (j+1) h' d c = succCell S₀ hzero j d (stageCell S₀ hzero i j h d c) :=
  Nat.leRecOn_succ (C:=fun i => RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) h c
lemma stageMap_chart (i j : ℕ) (h : i ≤ j) (d : ℕ)
    (c : RelCWComplex.cell (univ : Set (stageX S₀ hzero i)) d) (v : Fin d → ℝ) :
    stageMap S₀ hzero i j h (RelCWComplex.map d c v) =
      RelCWComplex.map d (stageCell S₀ hzero i j h d c) v := by
  induction j,h using Nat.le_induction with
  | base =>
    simp only [stageMap,stageCell,ContinuousMap.coe_mk,Function.Embedding.coeFn_mk,Nat.leRecOn_self]
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageCell_succ S₀ hzero i j h,ih]
    exact step_chart _ (attachments S₀ hzero j) d _ v
lemma stage_base (i j : ℕ) (h : i ≤ j) (a : stageI S₀ hzero i) (x : stageX S₀ hzero i) :
    x ∈ (stages S₀ hzero i).core.baseSet a ↔
      stageMap S₀ hzero i j h x ∈ (stages S₀ hzero j).core.baseSet (stageIndex S₀ hzero i j h a) := by
  induction j,h using Nat.le_induction with
  | base => simp only [DirectedSystem.map_self']
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageIndex_succ S₀ hzero i j h]
    exact ih.trans (step_base _ (attachments S₀ hzero j) _ _)
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationGeometry.FiniteStage
open Set Topology _root_.CategoryTheory CategoryTheory.Limits
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) m))
abbrev finalSpace := SequentialColimit.Space (stageX S₀ hzero) (stageMap S₀ hzero)
@[instance_reducible] noncomputable def finalCW : CWComplex (univ : Set (finalSpace S₀ hzero)) :=
  SequentialCW.cwComplex (stageX S₀ hzero) (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
    (stageCell S₀ hzero) (fun i j h d c v _ => stageMap_chart S₀ hzero i j h d c v)
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexRegular
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIndexRegular
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation FiniteExtension
variable {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
open scoped Classical TensorProduct MonoidAlgebra

noncomputable def embed : RegularProductR.rep ℤ K I ⟶
    Rep.res K.subtype (RegularProductR.rep ℤ L I) := Rep.ofHom ⟨embedLM K I, by
  intro k
  apply LinearMap.ext
  intro a
  funext i
  change Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)
    (RegularProductR.rightShift ℤ K k (a i)) =
    RegularProductR.rightShift ℤ L (k : L)
      (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L) (a i))
  have h : (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)).comp
      (RegularProductR.rightShift ℤ K k) =
      (RegularProductR.rightShift ℤ L (k : L)).comp
        (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)) := by
    apply Finsupp.lhom_ext
    intro x r
    simp
  exact LinearMap.congr_fun h (a i)⟩

noncomputable def eval : Rep.ind K.subtype (RegularProductR.rep ℤ K I) ⟶
    RegularProductR.rep ℤ L I :=
  (Rep.indResHomEquiv K.subtype (RegularProductR.rep ℤ K I)
    (RegularProductR.rep ℤ L I)).symm (embed K I)

lemma eval_mk {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
    (h : L) (a : RegularProductR.Module ℤ K I) (i : I) :
    eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a) i =
      Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*h) (a i) := by
  simp [eval, Rep.indResHomEquiv]
  change RegularProductR.rightShift ℤ L h⁻¹
    (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L) (a i)) = _
  rw [RegularProductR.rightShift, ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp]
  simp <;> rfl

lemma slices_eval_mk (c : Q K) (h : L) (a : RegularProductR.Module ℤ K I) :
    slices K I c (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a)) =
      if c = pi K h then (RegularProductR.rep ℤ K I).ρ (factor K h)⁻¹ a else 0 := by
  classical
  funext i
  change slice K c (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a) i) = _
  rw [eval_mk, ← LinearMap.comp_apply, slice_map]
  split_ifs <;> rfl

lemma ind_mk_left {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
    (k : K) (h : L) (a : RegularProductR.Module ℤ K I) :
    IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ ((k : L)*h) a =
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h
        ((RegularProductR.rep ℤ K I).ρ k⁻¹ a) := by
  simp

variable [Fintype (Q K)]
noncomputable def invLM : RegularProductR.Module ℤ L I →ₗ[ℤ]
    Representation.IndV K.subtype (RegularProductR.rep ℤ K I).ρ :=
  ∑ c, (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ (sectionMap K c)).comp (slices K I c)

lemma inv_eval_mk (h : L) (a : RegularProductR.Module ℤ K I) :
    invLM K I (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a)) =
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a := by
  let A := RegularProductR.rep ℤ K I
  calc
    _ = ∑ c : Q K, IndV.mk K.subtype A.ρ (sectionMap K c)
        (slices K I c (eval K I (IndV.mk K.subtype A.ρ h a))) := by
      exact LinearMap.sum_apply _ _ _
    _ = ∑ c : Q K, if c = pi K h then
        IndV.mk K.subtype A.ρ (sectionMap K c) (A.ρ (factor K h)⁻¹ a) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [slices_eval_mk]
      split_ifs
      · rfl
      · exact map_zero _
    _ = IndV.mk K.subtype A.ρ (sectionMap K (pi K h)) (A.ρ (factor K h)⁻¹ a) := by
      simp
    _ = IndV.mk K.subtype A.ρ h a := by
      rw [← ind_mk_left]
      congr 1
      simp [factor]
      rfl

lemma eval_inv (a : RegularProductR.Module ℤ L I) : eval K I (invLM K I a) = a := by
  funext i
  have he : invLM K I a = ∑ c : Q K,
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ (sectionMap K c) (slices K I c a) :=
    LinearMap.sum_apply _ _ _
  rw [he, map_sum, Finset.sum_apply]
  calc
    _ = ∑ c : Q K, Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*sectionMap K c)
        (slice K c (a i)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact eval_mk K I (sectionMap K c) (slices K I c a) i
    _ = a i := sum_slices K (a i)

lemma inv_eval (a : Rep.ind K.subtype (RegularProductR.rep ℤ K I)) :
    invLM K I (eval K I a) = a := by
  have h : (invLM K I).comp (eval K I).hom.toLinearMap = LinearMap.id := by
    apply IndV.hom_ext
    intro h
    ext a
    exact inv_eval_mk K I h a
  exact LinearMap.congr_fun h a

noncomputable def indIso : Rep.ind K.subtype (RegularProductR.rep ℤ K I) ≅
    RegularProductR.rep ℤ L I :=
  Rep.mkIso (Representation.Equiv.mk
    { (eval K I).hom.toLinearMap with
      invFun := invLM K I
      left_inv := inv_eval K I
      right_inv := eval_inv K I }
    (eval K I).hom.2)

end FiniteIndexRegular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolutionBeginningOfComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
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

namespace PresentationGeometry.FiniteStage
open Set Topology CWExtension CWEquivariant
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def algebraicBeginning (S : Stage G 0) : ProductFiniteResolution.Beginning (Rep.trivial ℤ G ℤ) := by
  let W := S.core
  letI := CoreDeck.leftAction W
  letI := CoreDeck.continuousLeftAction W (CoreDeck.of_potential W S.pot S.coord)
  let cov := DiscreteCoverCharts.covering W
  letI : T2Space W.TotalSpace := CoveringCellGeometry.hausdorff cov
  letI : Fact (∀ (g : G) (x : W.TotalSpace), W.proj (g • x) = W.proj x) := ⟨fun _ _ => rfl⟩
  letI : PathConnectedSpace (univ : Set W.TotalSpace) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_univ
  letI := CoveringCW.cwComplex_general cov
  letI : ∀ n, MulAction G (RelCWComplex.cell (univ : Set W.TotalSpace) n) :=
    fun n => EquivariantCoverCells.cellAction (p := W.proj) n
  have hc : ∀ (g : G) n (c : RelCWComplex.cell (univ : Set W.TotalSpace) n) (v : Disk n),
      g • RelCWComplex.map n c v = RelCWComplex.map n (g • c) v :=
    EquivariantCoverCells.chart_smul cov
  have e (n : ℕ) : object (G := G) (X := W.TotalSpace) n ≅
      Rep.free ℤ G (RelCWComplex.cell (univ : Set S.X) n) :=
    EquivariantCoverCells.freeIso (CoreDeck.left_free W) (CoreDeck.left_transitive W)
      (fun x => ⟨⟨x,(1:G)⟩,rfl⟩) n
  have he : (complex hc).ExactAt 1 := complex_exactAt hc 0 (by
    apply SingularAction.univ_homology_zero
    exact HurewiczConstruction.homology_zero_of_homotopy S.connectivity ⟨S.point,(1:G)⟩)
  letI : ∀ n, Finite (RelCWComplex.cell (univ : Set S.X) n) :=
    fun n => RelCWComplex.FiniteType.finite_cell n
  exact @ProductFiniteResolution.Beginning.ofComplex ℤ G _ _ (complex hc) (aug hc)
    (aug_epi hc) (d_aug hc) (aug_exact hc) he
    (fun n => RelCWComplex.cell (univ : Set S.X) n) inferInstance e
end PresentationGeometry.FiniteStage

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end OrbitBrown

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
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

lemma refines_refl (B : Basis ρ) : Refines ρ B B := fun b => ⟨b,GermBrick.restricts_refl ρ b.1⟩

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace FiniteIndexProducts
variable {G : Type} [Group G] (K : Subgroup G) [K.Normal] [K.FiniteIndex]
variable (I : Type) (n : ℕ)
def homologyIso : groupHomology (RegularProductR.rep ℤ K I) n ≅
    groupHomology (RegularProductR.rep ℤ G I) n := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  exact (groupHomology.indIso K (RegularProductR.rep ℤ K I) n).symm ≪≫
    (groupHomology.functor ℤ G n).mapIso (FiniteIndexRegular.indIso K I)

end FiniteIndexProducts

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

end OAI
end


