-- Prove2me | Definitions.Def_OAIQ043T004
-- name    : OAIQ043T004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:48:09.482673+00:00
-- url     : https://prove2.me/theorems/124f6c0b-88ec-4243-bbc4-11b099525122
-- title:
--   Definitions bundle OAIQ043T004 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 27 definitions, 1 inductive type or structure, 1 instance and 162 theorems. The definitions and types are `OAI.Thomason.AbstractTransfer.Boundaries.Cells`, `OAI.Thomason.AbstractTransfer.exactEndpoint`, `OAI.Thomason.AbstractTransfer.model`, `OAI.Thomason.AttachmentComparison.posetMap`, `OAI.Thomason.Attachments.constantFiniteAttachmentLabel`, `OAI.Thomason.Attachments.finitePosetObject`, `OAI.Thomason.Attachments.intervalFiberFullFiniteIso`, `OAI.Thomason.DirectedComplex.PartialHom`, `OAI.Thomason.GeometricRecognition.Contiguity.relativeVertices`, `OAI.Thomason.GeometricRecognition.PairRefinement.prepend`, `OAI.Thomason.GeometricRecognition.realizeCubeClasses`, `OAI.Thomason.GeometricRecognition.realizeCubeMap`, `OAI.Thomason.GeometricRecognition.simplexCubicalPair`, `OAI.Thomason.NormalizedChains.cutWord`, `OAI.Thomason.NormalizedChains.homVertex`, `OAI.Thomason.OmegaCategory.IsObjectCosieve`, `OAI.Thomason.OmegaCategory.chaoticFiniteFunctor`, `OAI.Thomason.OmegaCategory.face`, `OAI.Thomason.OmegaCategory.fullNerve`, `OAI.Thomason.OmegaCategory.fullNerveIso`, `OAI.Thomason.OmegaCategory.join`, `OAI.Thomason.OmegaCategory.objectsFiniteChaoticAdjunction`, `OAI.Thomason.OmegaCategory.objectsFiniteFunctor`, `OAI.Thomason.PartialNormalized.cutWord`, `OAI.Thomason.PartialNormalized.homTotal`, `OAI.Thomason.PartialNormalized.homVertex`, `OAI.Thomason.PartialNormalized.homWord`, `OAI.Thomason.SubdividedUnit.η`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_BoundaryQuotients`, `Thomason_CoherentGluing`, `Thomason_CubicalGeometry`, `Thomason_CubicalRecognition`, `Thomason_DimensionOne`, `Thomason_ExtensionAnodyne`, `Thomason_FiberRecognition`, `Thomason_FiniteAttachments`, `Thomason_Generators`, `Thomason_GlobularComplexes`, `Thomason_GrayGenerators`, `Thomason_KanQuillen`, `Thomason_KanTowers`, `Thomason_LabelledFibers`, `Thomason_Linearization`, `Thomason_ModelTransfer`, `Thomason_PartialTables`, `Thomason_PosetComparison`, `Thomason_PosetalColimits`, `Thomason_PosetalReduction`, `Thomason_ProperTransfer`, `Thomason_RelativeContiguity`, `Thomason_RelativeRepresentation`, `Thomason_SieveAttachments`, `Thomason_SimplexBoxes`, `Thomason_SimplicialApproximation`, `Thomason_SubdividedUnit`, `Thomason_SubdivisionMaps`, `Thomason_SubdivisionWeak`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T002` and `OAIQ043T003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T006` and `OAIQ043T007`; the proof of `OAI.Thomason.nerveDetection_allDimensions`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T002
import Definitions.Def_OAIQ043T003

section
-- module Solutions.OAIQ043_TH.Thomason_Linearization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteTables _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearization. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def IsObjectCosieve (C : OmegaCategory.{u}) (S : Set C.Objects) : Prop :=
  ∀ x : C.Cell, C.sourceObject x ∈ S → C.targetObject x ∈ S

open NormalizedChains

lemma simplex_objects_mem_cosieve {C : OmegaCategory.{u}} {m : ℕ}
    (F : Functor (Oriental m) C) {S : Set C.Objects} (hS : C.IsObjectCosieve S)
    (h0 : F.objects (tableObjectsEquiv.symm (0 : Fin (m+1))) ∈ S) :
    ∀ a : (Oriental m).Objects, F.objects a ∈ S := by
  intro a
  let i := tableObjectsEquiv a
  have h := hS (F.map (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)))
  have hs := (F.objects_source (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i))).symm
  have ht := (F.objects_target (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i))).symm
  have es : (Oriental m).sourceObject (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)) =
      tableObjectsEquiv.symm (0 : Fin (m+1)) := edgeTable_sourceObject _ _ _
  have et : (Oriental m).targetObject (edgeTable (0 : Fin (m+1)) i (Fin.zero_le i)) =
      tableObjectsEquiv.symm i := edgeTable_targetObject _ _ _
  rw [es] at hs
  rw [et] at ht
  rw [hs, ht] at h
  have hi := h h0
  have he : tableObjectsEquiv.symm i = a :=
    (tableObjectsEquiv (E := Fin (m+1))).symm_apply_apply a
  exact he ▸ hi

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

def fullNerve (C : OmegaCategory.{u}) (S : Set C.Objects) : (streetNerve C).Subcomplex where
  obj _ := {F | ∀ a, F.objects a ∈ S}
  map f _ h a := h ((orientals.map f.unop).objects a)

def fullNerveIso (C : OmegaCategory.{u}) (S : Set C.Objects) :
    streetNerve (C.fullOn S).category ≅ (C.fullNerve S : SSet.{u}) where
  hom := {
    app := fun _ => ↾fun F => ⟨Functor.comp F (C.fullOn S).inclusion,
      fun a => by
        have h := (F.map a.val).property.1
        change C.sourceObject ((Functor.comp F (C.fullOn S).inclusion).objects a).val ∈ S at h
        rwa [C.sourceObject_object] at h⟩
    naturality := fun _ _ _ => rfl }
  inv := {
    app := fun _ => ↾fun F => F.val.liftFullOn S F.property
    naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Functor.ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    rfl

lemma fullNerveIso_hom_ι (C : OmegaCategory.{u}) (S : Set C.Objects) :
    (C.fullNerveIso S).hom ≫ (C.fullNerve S).ι =
      streetNerveMap (C.fullOn S).inclusion := rfl

instance fullInclusion_nerve_mono (C : OmegaCategory.{u}) (S : Set C.Objects) :
    Mono (streetNerveMap (C.fullOn S).inclusion) := by
  rw [← fullNerveIso_hom_ι]
  infer_instance

lemma fullNerve_inf (C : OmegaCategory.{u}) (S T : Set C.Objects) :
    C.fullNerve (S ∩ T) = C.fullNerve S ⊓ C.fullNerve T := by
  ext n F
  exact forall_and

lemma fullNerve_cosieve_sup {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectCosieve S) (hT : C.IsObjectCosieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    C.fullNerve S ⊔ C.fullNerve T = ⊤ := by
  apply top_unique
  intro n F _
  rcases hcover (F.objects (NormalizedChains.tableObjectsEquiv.symm
      (0 : Fin (n.unop.len+1)))) with h | h
  · exact Or.inl (simplex_objects_mem_cosieve F hS h)
  · exact Or.inr (simplex_objects_mem_cosieve F hT h)

lemma fullNerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (h : C.fullNerve S ⊔ C.fullNerve T = ⊤) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) := by
  let sq : SSet.Subcomplex.BicartSq (C.fullNerve (S ∩ T))
      (C.fullNerve S) (C.fullNerve T) ⊤ := ⟨h, (C.fullNerve_inf S T).symm⟩
  exact sq.isPushout.of_iso (C.fullNerveIso (S ∩ T)).symm
    (C.fullNerveIso S).symm (C.fullNerveIso T).symm
    (SSet.Subcomplex.topIso (streetNerve C)) rfl rfl rfl rfl

lemma cosieve_cover_nerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectCosieve S) (hT : C.IsObjectCosieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) :=
  fullNerve_isPushout (fullNerve_cosieve_sup hS hT hcover)

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionMaps
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.LastVertexProof.intervalEnds_mono _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Maps. -/

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

theorem boundary_rlp_weak {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.I.rlp p) : simplicialWeakEquivalences p := by
  have hall : (MorphismProperty.monomorphisms SSet).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  let : HasLiftingProperty (initial.to B) p := hall _ inferInstance
  have sqs : CommSq (initial.to E) (initial.to B) p (𝟙 B) := ⟨Subsingleton.elim _ _⟩
  let s := sqs.lift
  have hs : s ≫ p = 𝟙 B := sqs.fac_right
  let : HasLiftingProperty (endsInclusion E) p := hall _ inferInstance
  have sq : CommSq (endsMap (p ≫ s) (𝟙 E)) (endsInclusion E) p (fst _ _ ≫ p) := by
    constructor
    ext k x
    cases x with
    | inl x =>
      change p.app k (s.app k (p.app k x)) = p.app k x
      exact congrArg (fun f : B ⟶ B => f.app k (p.app k x)) hs
    | inr x => rfl
  have h0 : SSet.ι₀ ≫ sq.lift = p ≫ s := by
    ext k x
    exact congrArg (fun f : Ends E ⟶ E => f.app k (Sum.inl x)) sq.fac_left
  have h1 : SSet.ι₁ ≫ sq.lift = 𝟙 E := by
    ext k x
    exact congrArg (fun f : Ends E ⟶ E => f.app k (Sum.inr x)) sq.fac_left
  have hl : simplicialWeakEquivalences sq.lift :=
    simplicialWeakEquivalences.of_precomp SSet.ι₁ sq.lift (endpoint_weak E).2
      (h1.symm ▸ simplicialWeakEquivalences.id_mem E)
  have hps : simplicialWeakEquivalences (p ≫ s) := h0 ▸
    simplicialWeakEquivalences.comp_mem _ _ (endpoint_weak E).1 hl
  have hr : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 E) s (by change 𝟙 E ≫ (p ≫ s) = p ≫ s; simp)
      r := Arrow.homMk (𝟙 E) p (by change 𝟙 E ≫ p = (p ≫ s) ≫ p; simp [Category.assoc,hs])
      retract := by ext <;> simp [hs] }
  exact simplicialWeakEquivalences.of_retract hr hps

end Thomason.SimplicialCylinder

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open SSet.modelCategoryQuillen

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

lemma boundary_right_weak : I.{u}.rlp ≤ simplicialWeakEquivalences :=
  fun _ _ p hp => SimplicialCylinder.boundary_rlp_weak p hp

lemma anodyne_weak : SSet.anodyneExtensions.{u} ≤ simplicialWeakEquivalences :=
  fun _ _ i hi => TopologicalHorn.anodyne_weak_equivalence i hi

end Thomason.KanQuillen

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularComplexes
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def face (C : OmegaCategory.{u}) (p : ℕ) (b : Bool) (x : C.Cell) : C.Cell :=
  if b then C.target p x else C.source p x

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BoundaryQuotients
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Quotients. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table OmegaCategory

structure PartialHom (K : DirectedComplex.{u}) (L : DirectedComplex.{v}) (n : ℕ) where
  map : (p : ℕ) → K.Chain p →+ L.Chain p
  map_d (p : ℕ) (hp : p < n) (x : K.Chain (p+1)) :
    map p (K.d p x) = L.d p (map (p+1) x)
  map_augmentation (x : K.Chain 0) : L.augmentation (map 0 x) = K.augmentation x
  map_positive (p : ℕ) (x : K.Chain p) :
    x ∈ K.positive p → map p x ∈ L.positive p

end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ExtensionAnodyne
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension Anodyne. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

theorem exComparison_weak (X : SSet.{u}) : simplicialWeakEquivalences (exComparison.app X) :=
  TopologicalHorn.anodyne_weak_equivalence _ (exComparison_anodyne X)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

theorem ex_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences (SSet.ex.map f) ↔ simplicialWeakEquivalences f := by
  have he := exComparison.naturality f
  constructor
  · intro h
    exact simplicialWeakEquivalences.of_postcomp f (exComparison.app Y)
      (exComparison_weak Y) (he.symm ▸ simplicialWeakEquivalences.comp_mem _ _ (exComparison_weak X) h)
  · intro h
    exact simplicialWeakEquivalences.of_precomp (exComparison.app X) (SSet.ex.map f)
      (exComparison_weak X) (he ▸ simplicialWeakEquivalences.comp_mem _ _ h (exComparison_weak Y))

lemma exSquared_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences ((SSet.ex ⋙ SSet.ex).map f) ↔ simplicialWeakEquivalences f := by
  change simplicialWeakEquivalences (SSet.ex.map (SSet.ex.map f)) ↔ _
  rw [ex_map_weak_iff, ex_map_weak_iff]

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionWeak
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

lemma exInfinity_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences (exInfinityFunctor.map f) ↔ simplicialWeakEquivalences f := by
  have he := exInfinityUnit.naturality f
  constructor
  · intro h
    exact simplicialWeakEquivalences.of_postcomp f (exInfinityComparison Y)
      (exInfinityComparison_weak Y)
      (he.symm ▸ simplicialWeakEquivalences.comp_mem _ _ (exInfinityComparison_weak X) h)
  · intro h
    exact simplicialWeakEquivalences.of_precomp (exInfinityComparison X) (exInfinityFunctor.map f)
      (exInfinityComparison_weak X)
      (he ▸ simplicialWeakEquivalences.comp_mem _ _ h (exInfinityComparison_weak Y))

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Generators
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generators. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def objectsFiniteFunctor (n : ℕ) : NCategory.{u} n ⥤ Type u :=
  nCategoryInclusion n ⋙ objectsFunctor

def chaoticFiniteFunctor (n : ℕ) (hn : 1 ≤ n) : Type u ⥤ NCategory.{u} n where
  obj S := ⟨chaotic S, fun x => (chaotic S).source_fixed_upwards hn rfl⟩
  map f := chaoticFunctor.map f

def objectsFiniteChaoticAdjunction (n : ℕ) (hn : 1 ≤ n) :
    objectsFiniteFunctor.{u} n ⊣ chaoticFiniteFunctor n hn :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun C S => TypeCat.homEquiv.trans (chaoticHomEquiv C.val S)
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

lemma objectsFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (objectsFiniteFunctor.{u} n) :=
  (objectsFiniteChaoticAdjunction n hn).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LabelledFibers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labelled Fibers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

lemma pushout_finite_objects (n : ℕ) (hn : 1 ≤ n) {A B C D : NCategory.{u} n}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f g h i) :
    IsPushout ((objectsFiniteFunctor n).map f) ((objectsFiniteFunctor n).map g)
      ((objectsFiniteFunctor n).map h) ((objectsFiniteFunctor n).map i) := by
  let : PreservesColimitsOfSize.{0,0} (objectsFiniteFunctor.{u} n) :=
    objectsFinite_preservesColimits n hn
  exact H.map _

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}}

lemma one_fiber_isObjectCosieve (p : Functor C interval.{u}) :
    C.IsObjectCosieve (intervalFiberObjects p 1) := by
  intro x hx
  apply Subtype.ext
  change p.map (C.target 0 x) = _
  rw [p.map_target]
  have he : p.map (C.source 0 x) = (intervalVertex 1).val := congrArg Subtype.val hx
  rw [p.map_source] at he
  have hl : (p.map x).left.down = 1 := congrArg (fun a => a.left.down) he
  have hr : (p.map x).right.down = 1 := le_antisymm
    (by exact Fin.le_last _) (by simpa only [hl] using (p.map x).related)
  apply ThinCell.ext <;> apply ULift.ext <;> exact hr

lemma minLabel_one_fiber (p q : Functor C interval.{u}) :
    ((minLabel p q).fiber (intervalVertex 1)).carrier =
      (p.fiber (intervalVertex 1)).carrier ∩ (q.fiber (intervalVertex 1)).carrier := by
  ext x
  change (minLabel p q).map x = (intervalVertex 1).val ↔
    p.map x = (intervalVertex 1).val ∧ q.map x = (intervalVertex 1).val
  simp only [intervalCell_eq_vertex_iff]
  rcases interval_cases (p.map x) with hp | hp | hp <;>
    rcases interval_cases (q.map x) with hq | hq | hq <;>
    simp [minLabel, hp, hq, intervalVertex, intervalArrow]

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetComparison
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poset Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma homTotal_map (f : Hom (complex E) (complex D)) (p : ℕ) (c : (complex E).Chain p) :
    homTotal f c.val = (f.map p c).val := by
  obtain ⟨c,hc⟩ := c
  apply grade_induction (M := fun c hc => homTotal f c =
    (f.map p ⟨c,hc⟩).val) ?_ ?_ ?_ ?_ c hc
  · rintro ⟨l,hl⟩ hlen
    rw [homTotal_bracket]
    cases l with
    | nil => simp at hlen
    | cons a l =>
      have he : l.length = p := by simpa using hlen
      subst p
      rfl
  · rw [map_zero]; exact (congrArg Subtype.val (f.map p).map_zero).symm
  · intro c d hc hd ihc ihd
    rw [map_add, ihc, ihd]
    exact (congrArg Subtype.val ((f.map p).map_add ⟨c,hc⟩ ⟨d,hd⟩)).symm
  · intro r c hc ih
    rw [map_smul,ih]
    exact (congrArg Subtype.val ((f.map p).map_zsmul r ⟨c,hc⟩)).symm

lemma homTotal_vertex_exists (f : Hom (complex E) (complex D)) (a : E) :
    ∃ b : D, homTotal f (bracket [a]) = bracket [b] := by
  apply positive_augmentation_one (homTotal_grade f (bracket_mem_grade [a]))
    (homTotal_positive f (bracket_positive [a]))
  rw [homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩]
  exact (f.map_augmentation ⟨bracket [a],bracket_mem_grade [a]⟩).trans (by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary,emptyCoefficient_bracket])

def homVertex (f : Hom (complex E) (complex D)) (a : E) : D :=
  (homTotal_vertex_exists f a).choose

def cutWord (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) (l : List E) : Chains D :=
  l.reverseRecOn (bracket []) (fun l a c =>
    if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) c)

@[simp] lemma cutWord_nil (f : Hom (complex E) (complex D)) (θ : E →o Fin 2) :
    cutWord f θ [] = bracket [] := by
  unfold cutWord
  exact List.reverseRecOn_nil _ _

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PartialTables
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Tables. -/

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

def homWord (f : PartialHom (complex E) (complex D) n) : List E → Chains D
  | [] => bracket []
  | a :: l => (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).val

def homTotal (f : PartialHom (complex E) (complex D) n) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l => homWord f l.val)

lemma homTotal_bracket (f : PartialHom (complex E) (complex D) n) (l : List E) :
    homTotal f (bracket l) = homWord f l := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ _ (Finsupp.single _ 1) = _
    rw [Finsupp.linearCombination_single, one_smul]
  · rw [bracket_of_not_pairwise h, map_zero]
    cases l with
    | nil => exact (h (by simp)).elim
    | cons a l =>
      change 0 = (f.map l.length (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length)).val
      have he : (⟨bracket (a::l), bracket_mem_grade (a::l)⟩ : (complex E).Chain l.length) = 0 :=
        Subtype.ext (bracket_of_not_pairwise h)
      erw [he, map_zero]; rfl

lemma homTotal_grade (f : PartialHom (complex E) (complex D) n) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) : homTotal f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  rintro ⟨l,hl⟩ hlen
  subst k
  cases l with
  | nil => exact bracket_mem_grade ([] : List D)
  | cons a l => exact (f.map l.length ⟨bracket (a::l), bracket_mem_grade (a::l)⟩).property

lemma homTotal_map (f : PartialHom (complex E) (complex D) n) (p : ℕ) (c : (complex E).Chain p) :
    homTotal f c.val = (f.map p c).val := by
  obtain ⟨c,hc⟩ := c
  apply grade_induction (M := fun c hc => homTotal f c =
    (f.map p ⟨c,hc⟩).val) ?_ ?_ ?_ ?_ c hc
  · rintro ⟨l,hl⟩ hlen
    rw [homTotal_bracket]
    cases l with
    | nil => simp at hlen
    | cons a l =>
      have he : l.length = p := by simpa using hlen
      subst p
      rfl
  · rw [map_zero]; exact (congrArg Subtype.val (f.map p).map_zero).symm
  · intro c d hc hd ihc ihd
    rw [map_add, ihc, ihd]
    exact (congrArg Subtype.val ((f.map p).map_add ⟨c,hc⟩ ⟨d,hd⟩)).symm
  · intro r c hc ih
    rw [map_smul,ih]
    exact (congrArg Subtype.val ((f.map p).map_zsmul r ⟨c,hc⟩)).symm

lemma homTotal_positive (f : PartialHom (complex E) (complex D) n) {c : Chains E}
    (hc : Positive c) : Positive (homTotal f c) := by
  apply linearCombination_positive _ ?_ hc
  rintro ⟨l,hl⟩
  cases l with
  | nil => exact bracket_positive []
  | cons a l => exact f.map_positive l.length _ (bracket_positive _)

lemma homTotal_vertex_exists (f : PartialHom (complex E) (complex D) n) (a : E) :
    ∃ b : D, homTotal f (bracket [a]) = bracket [b] := by
  apply positive_augmentation_one (homTotal_grade f (bracket_mem_grade [a]))
    (homTotal_positive f (bracket_positive [a]))
  rw [homTotal_map f 0 ⟨bracket [a],bracket_mem_grade [a]⟩]
  exact (f.map_augmentation ⟨bracket [a],bracket_mem_grade [a]⟩).trans (by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary,emptyCoefficient_bracket])

def homVertex (f : PartialHom (complex E) (complex D) n) (a : E) : D :=
  (homTotal_vertex_exists f a).choose

def cutWord (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) (l : List E) : Chains D :=
  l.reverseRecOn (bracket []) (fun l a c =>
    if θ a = 0 then homTotal f (bracket (l++[a])) else append (homVertex f a) c)

@[simp] lemma cutWord_nil (f : PartialHom (complex E) (complex D) n) (θ : E →o Fin 2) :
    cutWord f θ [] = bracket [] := by
  unfold cutWord
  exact List.reverseRecOn_nil _ _

end Thomason.PartialNormalized

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SieveAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

open NormalizedChains.PosetTables

lemma posetLabel_constant {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (e : Fin 2) (hl : ∀ p, l p = e) :
    posetCategorificationLabel l = constantLabel (categorification.obj (nerve P)) e := by
  apply OmegaCategory.Functor.ext
  funext x
  apply ThinCell.ext <;> apply ULift.ext <;> exact hl _

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma tableLabel_objects {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : (NormalizedChains.complex P).nu.Objects) :
    (tableLabel l).objects x = intervalVertex (l (NormalizedChains.tableObjectsEquiv x)) := by
  apply Subtype.ext
  apply ThinCell.ext <;> apply ULift.ext
  · exact congrArg l (congrArg NormalizedChains.tableObjectsEquiv
      ((NormalizedChains.complex P).nu.sourceObject_object x))
  · exact congrArg l (congrArg NormalizedChains.tableObjectsEquiv
      ((NormalizedChains.complex P).nu.targetObject_object x))

lemma posetLabel_objects {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : (categorification.obj (nerve P)).Objects) :
    (posetCategorificationLabel l).objects x = intervalVertex
      (l (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x))) := by
  change (tableLabel l).objects ((posetCategorificationTableMap P).objects x) = _
  exact tableLabel_objects l _

lemma interval_vertex_mem_old {X Y : OmegaCategory.{u}} (h : X ⟶ Y)
    (η : Y ⟶ interval) (e : Fin 2) (he : h ≫ η = constantLabel X e) (x : X.Objects) :
    h.objects x ∈ intervalFiberObjects η e := by
  exact congrArg (fun f : X ⟶ interval => f.objects x) he

lemma minLabel_objects_fiber {C : OmegaCategory.{u}} (p q : C ⟶ interval) :
    intervalFiberObjects (minLabel p q) 1 =
      intervalFiberObjects p 1 ∩ intervalFiberObjects q 1 := by
  ext x
  change (minLabel p q).objects x = intervalVertex 1 ↔
    p.objects x = intervalVertex 1 ∧ q.objects x = intervalVertex 1
  erw [← Subtype.val_inj,← Subtype.val_inj,← Subtype.val_inj]
  exact Set.ext_iff.mp (minLabel_one_fiber p q) x.val

end Thomason.Attachments

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma posetFiniteLabel_constant (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (e : Fin 2) (hl : ∀ p, l p = e) :
    posetCategorificationFiniteLabel n hn l =
      constantLabel ((categorificationFinite n).obj (nerve P)).val e := by
  apply truncation_functor_ext
  exact posetLabel_constant l e hl

lemma posetFiniteLabel_natural (n : ℕ) (hn : 1 ≤ n)
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (g : Q →o P) (l : P →o Fin 2) :
    (categorificationFinite n).map (nerveMap g.monotone.functor) ≫
      posetCategorificationFiniteLabel n hn l = posetCategorificationFiniteLabel n hn (l.comp g) := by
  apply truncation_functor_ext
  exact posetCategorificationLabel_natural g l

lemma posetFiniteLabel_min (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l₁ l₂ : P →o Fin 2) :
    posetCategorificationFiniteLabel n hn
      (⟨fun p => min (l₁ p) (l₂ p),fun _ _ he => min_le_min (l₁.monotone he) (l₂.monotone he)⟩ : P →o Fin 2) =
      minLabel (posetCategorificationFiniteLabel n hn l₁) (posetCategorificationFiniteLabel n hn l₂) := by
  apply truncation_functor_ext
  rfl

variable (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

def constantFiniteAttachmentLabel : Y ⟶ finiteInterval n hn :=
  H.desc (constantFiniteLabel n hn X b) (posetCategorificationFiniteLabel n hn l) (by
    rw [comp_constantFiniteLabel]
    exact ((posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA)).symm)

lemma constantFiniteAttachmentLabel_old :
    h ≫ constantFiniteAttachmentLabel n hn A l b hlA a h i H = constantFiniteLabel n hn X b := H.inl_desc _ _ _
lemma constantFiniteAttachmentLabel_new :
    i ≫ constantFiniteAttachmentLabel n hn A l b hlA a h i H = posetCategorificationFiniteLabel n hn l := H.inr_desc _ _ _

lemma subposetFiniteMap_comp (S : Set P) (hAS : A ⊆ S) :
    (categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
      (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) =
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor) := by
  rw [← (categorificationFinite n).map_comp]
  rfl

def intervalFiberFullFiniteIso {C : NCategory.{u} n} (η : C ⟶ finiteInterval n hn) (e : Fin 2) :
    (fiberFiniteFunctor n hn e).obj (Over.mk η) ≅ fullFinite n C (intervalFiberObjects η e) where
  hom := (intervalFiberFullIso η e).hom
  inv := (intervalFiberFullIso η e).inv
  hom_inv_id := (intervalFiberFullIso η e).hom_inv_id
  inv_hom_id := (intervalFiberFullIso η e).inv_hom_id

lemma constant_finite_attachment_old_piece (S : Set P) (hAS : A ⊆ S)
    (hS : S = {p | l p = b}) :
    IsPosetFiniteAttachmentPiece n A S hAS a h i
      (intervalFiberObjects (constantFiniteAttachmentLabel n hn A l b hlA a h i H) b) := by
  let η := constantFiniteAttachmentLabel n hn A l b hlA a h i H
  let q := posetCategorificationFiniteLabel n hn l
  let C := (categorificationFinite n).obj (nerve A)
  let g : C ⟶ (categorificationFinite n).obj (nerve P) :=
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn C b)
  let old : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantFiniteAttachmentLabel_old n hn A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantFiniteAttachmentLabel_new n hn A l b hlA a h i H)
  let F := fiberFiniteFunctor n hn b
  let E := posetPieceFiniteFiberIso n hn S l b hS
  let j := (constantFiniteFiberIso n hn X b).hom ≫ F.map hf
  let k := E.hom ≫ F.map if'
  have := fiberFiniteInclusion_mono n hn b (Over.mk q)
  have hE := posetPieceFiniteFiberIso_inclusion n hn S l b hS
  have hp : IsPushout a
      ((categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor)) j k := by
    refine (labelled_pushout_finite_fibers n hn af gf hf if' H b).of_iso'
      (constantFiniteFiberIso n hn C b) (constantFiniteFiberIso n hn X b) E (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · apply (cancel_mono (C := NCategory.{u} n) (fiberFiniteInclusion n hn b (Over.mk q))).mp
      change g = (categorificationFinite n).map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
        (E.hom ≫ fiberFiniteInclusion n hn b (Over.mk q))
      rw [hE]
      exact (subposetFiniteMap_comp n A S hAS).symm
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
  let Efull := intervalFiberFullFiniteIso n hn η b
  refine ⟨j ≫ Efull.hom,k ≫ Efull.hom,?_,?_,?_⟩
  · rfl
  · change k ≫ fiberFiniteInclusion n hn b (Over.mk η) = _
    change E.hom ≫ (F.map if' ≫ fiberFiniteInclusion n hn b (Over.mk η)) = _
    change E.hom ≫ (fiberFiniteInclusion n hn b (Over.mk q) ≫ i) = _
    rw [← Category.assoc, hE]
  · exact hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) Efull
      (by simp) (by simp) (by simp) (by simp)

lemma constant_finite_attachment_new_piece (S : Set P) (e : Fin 2) (hbe : b ≠ e)
    (hS : S = {p | l p = e}) :
    IsPosetFiniteNewPiece n S i (intervalFiberObjects (constantFiniteAttachmentLabel n hn A l b hlA a h i H) e) := by
  let η := constantFiniteAttachmentLabel n hn A l b hlA a h i H
  let q := posetCategorificationFiniteLabel n hn l
  let C := (categorificationFinite n).obj (nerve A)
  let g : C ⟶ (categorificationFinite n).obj (nerve P) :=
    (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn C b)
  let old : Over (finiteInterval n hn) := Over.mk (constantFiniteLabel n hn X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetFiniteLabel_natural n hn _ l).trans (posetFiniteLabel_constant n hn _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantFiniteAttachmentLabel_old n hn A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantFiniteAttachmentLabel_new n hn A l b hlA a h i H)
  let F := fiberFiniteFunctor n hn e
  have : IsEmpty (F.obj src).val.Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsEmpty (F.obj old).val.Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  let J := isoOfBijective ((nCategoryInclusion n).map (F.map af)) (by
    constructor
    · intro x; change (F.obj src).val.Cell at x; exact isEmptyElim x
    · intro x; change (F.obj old).val.Cell at x; exact isEmptyElim x)
  let Jf : F.obj src ≅ F.obj old := {
    hom := J.hom, inv := J.inv, hom_inv_id := J.hom_inv_id, inv_hom_id := J.inv_hom_id }
  have : IsIso (F.map af) := Jf.isIso_hom
  have hp := labelled_pushout_finite_fibers n hn af gf hf if' H e
  have : IsIso (F.map if') := hp.isIso_inr_of_isIso
  let E := posetPieceFiniteFiberIso n hn S l e hS
  let fiberIso := asIso (F.map if')
  refine ⟨E ≪≫ fiberIso ≪≫ intervalFiberFullFiniteIso n hn η e, ?_⟩
  change E.hom ≫ (F.map if' ≫ fiberFiniteInclusion n hn e (Over.mk η)) = _
  change E.hom ≫ (fiberFiniteInclusion n hn e (Over.mk q) ≫ i) = _
  rw [← Category.assoc, posetPieceFiniteFiberIso_inclusion n hn]

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

def finitePosetObject (n : ℕ) {P : Type u} [PartialOrder P]
    (x : ((categorificationFinite n).obj (nerve P)).val.Objects) : P :=
  NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects
    (truncationCellLift (categorification.obj (nerve P)) n 0 x))

lemma posetFiniteLabel_objects (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : ((categorificationFinite n).obj (nerve P)).val.Objects) :
    (posetCategorificationFiniteLabel n hn l).objects x = intervalVertex (l (finitePosetObject n x)) := by
  conv_lhs => rw [← truncationCellLift_unit (categorification.obj (nerve P)) n 0 x]
  exact posetLabel_objects l (truncationCellLift (categorification.obj (nerve P)) n 0 x)

lemma labelled_finite_objects_cover (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] {A : Set P}
    {X Y : NCategory.{u} n} {a : (categorificationFinite n).obj (nerve A) ⟶ X}
    {h : X ⟶ Y} {i : (categorificationFinite n).obj (nerve P) ⟶ Y}
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)
    (η₁ η₂ : Y ⟶ finiteInterval n hn) (l₁ l₂ : P →o Fin 2) (e : Fin 2)
    (hh : h ≫ η₁ = constantFiniteLabel n hn X e ∨ h ≫ η₂ = constantFiniteLabel n hn X e)
    (hi₁ : i ≫ η₁ = posetCategorificationFiniteLabel n hn l₁)
    (hi₂ : i ≫ η₂ = posetCategorificationFiniteLabel n hn l₂)
    (hl : ∀ p, l₁ p = e ∨ l₂ p = e) :
    intervalFiberObjects η₁ e ∪ intervalFiberObjects η₂ e = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases Types.eq_or_eq_of_isPushout (pushout_finite_objects n hn _ _ _ _ H) y with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rcases hh with hh | hh
    · exact Or.inl (interval_vertex_mem_old h η₁ e hh x)
    · exact Or.inr (interval_vertex_mem_old h η₂ e hh x)
  · rcases hl (finitePosetObject n x) with hx | hx
    · apply Or.inl
      change η₁.objects (i.objects x) = intervalVertex e
      exact (congrArg (fun f : (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn => f.objects x) hi₁).trans
        ((posetFiniteLabel_objects n hn l₁ x).trans (congrArg intervalVertex hx))
    · apply Or.inr
      change η₂.objects (i.objects x) = intervalVertex e
      exact (congrArg (fun f : (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn => f.objects x) hi₂).trans
        ((posetFiniteLabel_objects n hn l₂ x).trans (congrArg intervalVertex hx))

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma minFiniteLabel_objects_fiber (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) :
    intervalFiberObjects (minFiniteLabel n hn p q) 1 = intervalFiberObjects p 1 ∩ intervalFiberObjects q 1 :=
  minLabel_objects_fiber p q

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

theorem cosieve_finite_attachment_covers (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsUpperSet S₁) (h₂ : IsUpperSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : Disjoint A S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.val.Objects,
      Y.val.IsObjectCosieve T₁ ∧ Y.val.IsObjectCosieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetFiniteAttachmentPiece n A S₁ hA₁ a h i T₁ ∧
      IsPosetFiniteNewPiece n S₂ i T₂ ∧ IsPosetFiniteNewPiece n (S₁ ∩ S₂) i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := upperSegmentLabel S₁ h₁
  let l₂ := upperSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => min (l₁ p) (l₂ p),
    fun _ _ he => min_le_min (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 1 := fun p => (upperSegmentLabel_one S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := by
    intro p
    have hp : p.val ∉ S₂ := fun hp => Set.disjoint_left.mp hA₂ p.property hp
    change (if p.val ∈ S₂ then (1 : Fin 2) else 0) = 0
    simp [hp]
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change min (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 1} := by ext p; exact (upperSegmentLabel_one S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 1} := by ext p; exact (upperSegmentLabel_one S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 1} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      min (if p ∈ S₁ then (1 : Fin 2) else 0) (if p ∈ S₂ then 1 else 0) = 1
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantFiniteAttachmentLabel n hn A l₁ 1 hl₁ a h i H
  let η₂ := constantFiniteAttachmentLabel n hn A l₂ 0 hl₂ a h i H
  let η₃ := constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = minFiniteLabel n hn η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_old n hn,comp_minFiniteLabel,
        constantFiniteAttachmentLabel_old n hn,constantFiniteAttachmentLabel_old n hn]
      rfl
    · change i ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_new n hn,comp_minFiniteLabel,
        constantFiniteAttachmentLabel_new n hn,constantFiniteAttachmentLabel_new n hn]
      exact posetFiniteLabel_min n hn l₁ l₂
  have hp₃ := constant_finite_attachment_new_piece n hn A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) 1 (by decide) hS₃
  change IsPosetFiniteNewPiece n (S₁ ∩ S₂) i (intervalFiberObjects η₃ 1) at hp₃
  rw [hη₃,minFiniteLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 1,intervalFiberObjects η₂ 1,
    one_fiber_isObjectCosieve η₁,one_fiber_isObjectCosieve η₂,?_,
    constant_finite_attachment_old_piece n hn A l₁ 1 hl₁ a h i H S₁ hA₁ hS₁,
    constant_finite_attachment_new_piece n hn A l₂ 0 hl₂ a h i H S₂ 1 (by decide) hS₂,hp₃⟩
  refine labelled_finite_objects_cover n hn H η₁ η₂ l₁ l₂ 1
    (Or.inl (constantFiniteAttachmentLabel_old n hn A l₁ 1 hl₁ a h i H))
    (constantFiniteAttachmentLabel_new n hn A l₁ 1 hl₁ a h i H)
    (constantFiniteAttachmentLabel_new n hn A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((upperSegmentLabel_one S₁ h₁ p).mpr) ((upperSegmentLabel_one S₂ h₂ p).mpr)

end Thomason.Attachments

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdividedUnit
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivided Unit. -/

noncomputable section
universe u v w z


namespace Thomason.LastVertexProof
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

lemma lastVertex_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (Subdivision.lastVertex.app X) := by
  let A := SSet.sd.obj X
  let R := Subdivision.exInfinityFunctor
  let eA : A ⟶ R.obj A := Subdivision.exInfinityComparison A
  let eX : X ⟶ R.obj X := Subdivision.exInfinityComparison X
  let l := Subdivision.lastVertex.app X
  let : SSet.KanComplex (R.obj A) := Subdivision.exInfinity_kan A
  let : SSet.KanComplex (R.obj X) := Subdivision.exInfinity_kan X
  obtain ⟨t, Ht⟩ := precomp_lastVertex_surjective X (R.obj A) eA
  have Ht' := homotopic_post Ht (R.map l)
  have he : eA ≫ R.map l = l ≫ eX :=
    Subdivision.exInfinityInclusion_naturality l 0
  rw [he, Category.assoc] at Ht'
  have H := precomp_lastVertex_injective X (R.obj X) (t ≫ R.map l) eX Ht'
  have hlt : simplicialWeakEquivalences (l ≫ t) :=
    (homotopic_weak_iff Ht).mpr (Subdivision.exInfinityComparison_weak A)
  have htr : simplicialWeakEquivalences (t ≫ R.map l) :=
    (homotopic_weak_iff H).mpr (Subdivision.exInfinityComparison_weak X)
  exact simplicialWeakEquivalences.of_postcomp l t
    (simplicialWeakEquivalences_middle l t (R.map l) hlt htr) hlt

end Thomason.LastVertexProof

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision
open CategoryTheory

theorem lastVertex_weak : LastVertexStatement.{u} := LastVertexProof.lastVertex_weak

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.KanHomotopy
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open HornSubdivision LastVertexProof

lemma homotopy_equivalence_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsHomotopyEquivalence f) : simplicialWeakEquivalences f := by
  obtain ⟨g,hg,hf⟩ := hf
  have hfg := (homotopic_weak_iff hg).mpr (simplicialWeakEquivalences.id_mem X)
  have hgf := (homotopic_weak_iff hf).mpr (simplicialWeakEquivalences.id_mem Y)
  exact simplicialWeakEquivalences.of_postcomp f g
    (simplicialWeakEquivalences_middle f g f hfg hgf) hfg

end Thomason.KanHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CoherentGluing
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coherent Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy

lemma local_heq {A B : SSet.{u}} (f : A ⟶ B) (hf : IsHomotopyEquivalence f) : Local f := by
  intro K hK
  obtain ⟨g,hg,hh⟩ := hf
  refine ⟨(pre g).app K, ?_, ?_⟩
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using homotopic_pre_map hh K
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using homotopic_pre_map hg K

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory OmegaCategory

lemma nerve_categorification_attach {C : Cat.{u,u}} {X : NCategory.{u} 1}
    (a : (categorificationFinite 1).obj (nerveFunctor.obj C) ⟶ X) :
    nerveFunctor.map ((categorificationCatIso C).hom ≫ oneSkeletonCatFunctor.map a) =
      (categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫
        (streetNerveFinite 1).map a ≫ oneNerveFunctorIso.hom.app X := by
  rw [CategoryTheory.Functor.map_comp, categorificationCatIso_nerve]
  erw [Category.assoc]

lemma finite_poset_comparison_coherent {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (r : E →o A) (ri : ∀ a, r (i a) = a)
    (counit : ∀ e, i (r e) ≤ e)
    {X Y : NCategory.{u} 1}
    {a : (categorificationFinite 1).obj (nerve A) ⟶ X}
    {j : X ⟶ Y} {v : (categorificationFinite 1).obj (nerve E) ⟶ Y}
    (sc : IsPushout a ((categorificationFinite 1).map (nerveMap i.toFunctor)) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite 1).obj X ⟶ P}
    {lE : (streetNerveFinite 1).obj ((categorificationFinite 1).obj (nerve E)) ⟶ P}
    (ss : IsPushout ((streetNerveFinite 1).map a)
      ((streetNerveFinite 1).map ((categorificationFinite 1).map (nerveMap i.toFunctor))) lX lE)
    (F : P ⟶ (streetNerveFinite 1).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite 1).map j)
    (hFE : lE ≫ F = (streetNerveFinite 1).map v) : CoherentGluing.Coherent F := by
  let sk := oneSkeletonCatFunctor
  let N := streetNerveFinite 1
  let a' := (categorificationCatIso (Cat.of A)).hom ≫ sk.map a
  let v' := (categorificationCatIso (Cat.of E)).hom ≫ sk.map v
  have sc' : IsPushout a' i.toFunctor.toCatHom (sk.map j) v' := by
    apply (sc.map sk).of_iso' (categorificationCatIso (Cat.of A)) (Iso.refl _)
      (categorificationCatIso (Cat.of E)) (Iso.refl _)
    · simp [a']
      rfl
    · exact (categorificationCatIso_natural i.toFunctor.toCatHom).symm
    · simp
    · simp [v']
      rfl
  let dX := oneNerveFunctorIso.app X
  let dY := oneNerveFunctorIso.app Y
  let uA := (categorificationFiniteAdjunction 1).unit.app (nerve A)
  let uE := (categorificationFiniteAdjunction 1).unit.app (nerve E)
  have : IsIso uA := oneUnitCatIso (Cat.of A)
  have : IsIso uE := oneUnitCatIso (Cat.of E)
  have ha' : nerveFunctor.map a' = uA ≫ N.map a ≫ dX.hom :=
    nerve_categorification_attach (C := Cat.of A) a
  have hv' : nerveFunctor.map v' = uE ≫ N.map v ≫ dY.hom :=
    nerve_categorification_attach (C := Cat.of E) v
  have ss' : IsPushout (nerveFunctor.map a') (nerveMap i.toFunctor)
      (dX.inv ≫ lX) (uE ≫ lE) := by
    apply ss.of_iso' (asIso uA) dX.symm (asIso uE) (Iso.refl _)
    · simp only [asIso_hom, ha', Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.symm_hom]
      rfl
    · exact ((categorificationFiniteAdjunction 1).unit.naturality (nerveMap i.toFunctor)).symm
    · simp
    · simp
  have hf'X : (dX.inv ≫ lX) ≫ (F ≫ dY.hom) = nerveFunctor.map (sk.map j) := by
    rw [Category.assoc, ← Category.assoc lX F, hFX]
    rw [show N.map j ≫ dY.hom = dX.hom ≫ nerveFunctor.map (sk.map j) from
      oneNerveFunctorIso.hom.naturality j]
    erw [Iso.inv_hom_id_assoc]
  have hf'E : (uE ≫ lE) ≫ (F ≫ dY.hom) = nerveFunctor.map v' := by
    rw [Category.assoc, ← Category.assoc lE F, hFE, hv']
  apply CoherentGluing.coherent_of_postIso F dY
  exact nerve_pushout_coherent sc' r.toFunctor.toCatHom
    (posetMapRetraction i r ri) (posetMapCylinder i r counit)
    (posetMapCylinder_zero i r counit) (posetMapCylinder_one i r counit)
    (posetMapCylinder_stationary i r ri counit) ss' (F ≫ dY.hom) hf'X hf'E
end Thomason.OneCat

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments

abbrev posetMap (n : ℕ) {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :=
  (categorificationFinite n).map (nerveMap f.toFunctor)

lemma attachment_nerve_cover (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAZ : A ⊆ Z) (hAC : Disjoint A C) (hcover : Z ∪ C = Set.univ)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X) (j : X ⟶ Y)
    (v : posetObj n P ⟶ Y) (sc : IsPushout a (inc n A) j v) :
    ∃ (YZ : NCategory.{u} n) (jZ : X ⟶ YZ) (vZ : posetObj n Z ⟶ YZ) (uZ : YZ ⟶ Y),
      IsPushout a (sb n A Z hAZ) jZ vZ ∧ jZ ≫ uZ = j ∧ vZ ≫ uZ = inc n Z ≫ v ∧
      IsPushout ((streetNerveFinite n).map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ))
        ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right))
        ((streetNerveFinite n).map uZ) ((streetNerveFinite n).map (inc n C ≫ v)) := by
  obtain ⟨T₁,T₂,hT₁,hT₂,hTc,⟨jZ,vZ,hj,hv,sz⟩,⟨e₂,he₂⟩,⟨e₃,he₃⟩⟩ :=
    cosieve_finite_attachment_covers n hn A Z C hZ hC hAZ hAC hcover a j v sc
  let N := streetNerveFinite n
  let u₁ := fullFiniteInclusion n Y T₁
  let u₂ := fullFiniteInclusion n Y T₂
  let u₃ := fullFiniteInclusion n Y (T₁ ∩ T₂)
  let p₁ : fullFinite n Y (T₁ ∩ T₂) ⟶ fullFinite n Y T₁ :=
    fullOnMap Set.inter_subset_left
  let p₂ : fullFinite n Y (T₁ ∩ T₂) ⟶ fullFinite n Y T₂ :=
    fullOnMap Set.inter_subset_right
  change vZ ≫ u₁ = inc n Z ≫ v at hv
  change e₂.hom ≫ u₂ = inc n C ≫ v at he₂
  change e₃.hom ≫ u₃ = inc n (Z ∩ C) ≫ v at he₃
  have hu₁ : p₁ ≫ u₁ = u₃ := rfl
  have hu₂ : p₂ ≫ u₂ = u₃ := rfl
  have : Mono (N.map u₁) := fullInclusion_nerve_mono Y.val T₁
  have : Mono (N.map u₂) := fullInclusion_nerve_mono Y.val T₂
  have sq : IsPushout (N.map p₁) (N.map p₂) (N.map u₁) (N.map u₂) :=
    cosieve_cover_nerve_isPushout hT₁ hT₂ (fun x => by
      have hx : x ∈ T₁ ∪ T₂ := by rw [hTc]; trivial
      exact hx)
  refine ⟨fullFinite n Y T₁, jZ, vZ, u₁, sz, hj, hv, ?_⟩
  apply sq.of_iso' (N.mapIso e₃) (Iso.refl _) (N.mapIso e₂) (Iso.refl _)
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₃.hom ≫ N.map p₁ = N.map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ)
    apply (cancel_mono (N.map u₁)).mp
    simp only [← N.map_comp, Category.assoc, hu₁, he₃, hv]
    rw [sb_inc_assoc]
  · simp only [CategoryTheory.Functor.mapIso_hom]
    change N.map e₃.hom ≫ N.map p₂ = N.map (sb n (Z ∩ C) C Set.inter_subset_right) ≫ N.map e₂.hom
    apply (cancel_mono (N.map u₂)).mp
    simp only [← N.map_comp, Category.assoc, hu₂, he₃, he₂]
    rw [sb_inc_assoc]
  · simp [N]
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₂.hom ≫ N.map u₂ = N.map (inc n C ≫ v)
    rw [← N.map_comp, he₂]

lemma poset_nerve_cover (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hcover : Z ∪ C = Set.univ) :
    IsPushout ((streetNerveFinite n).map (sb n (Z ∩ C) Z Set.inter_subset_left))
      ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right))
      ((streetNerveFinite n).map (inc n Z)) ((streetNerveFinite n).map (inc n C)) := by
  obtain ⟨YZ,jZ,vZ,uZ,sz,hj,hv,sq⟩ := attachment_nerve_cover n hn (∅ : Set P) Z C
    hZ hC (Set.empty_subset Z) (by simp) hcover
    (𝟙 (posetObj n (∅ : Set P))) (inc n (∅ : Set P)) (𝟙 (posetObj n P))
    (IsPushout.of_id_fst)
  have : IsIso vZ := sz.isIso_inr_of_isIso
  let N := streetNerveFinite n
  apply sq.of_iso' (Iso.refl _) (N.mapIso (asIso vZ)) (Iso.refl _) (Iso.refl _)
  · simp [N]
  · simp
  · simp only [CategoryTheory.Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map vZ ≫ N.map uZ = N.map (inc n Z)
    rw [← N.map_comp, hv, Category.comp_id]
  · simp
end Thomason.AttachmentComparison

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanTowers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Towers. -/

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments OneCat

lemma one_nerve_mono_orderMap {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (hi : Function.Injective i) :
    Mono ((streetNerveFinite 1).map (posetMap 1 i)) := by
  let ηA := (categorificationFiniteAdjunction 1).unit.app (nerve A)
  let ηE := (categorificationFiniteAdjunction 1).unit.app (nerve E)
  have : IsIso ηA := oneUnitCatIso (Cat.of A)
  have : IsIso ηE := oneUnitCatIso (Cat.of E)
  have : Mono (nerveMap i.toFunctor) := nerve_mono_orderMap i hi
  have he : (streetNerveFinite 1).map (posetMap 1 i) =
      inv ηA ≫ nerveMap i.toFunctor ≫ ηE := by
    apply (cancel_epi ηA).mp
    rw [IsIso.hom_inv_id_assoc]
    exact ((categorificationFiniteAdjunction 1).unit.naturality (nerveMap i.toFunctor)).symm
  rw [he]
  infer_instance
end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments OneCat

lemma comparison_local_one {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : NCategory.{u} 1} (a : posetObj 1 A ⟶ X)
    (j : X ⟶ Y) (v : posetObj 1 B ⟶ Y) (sc : IsPushout a (inc 1 A) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite 1).obj X ⟶ P}
    {lB : (streetNerveFinite 1).obj (posetObj 1 B) ⟶ P}
    (ss : IsPushout ((streetNerveFinite 1).map a) ((streetNerveFinite 1).map (inc 1 A)) lX lB)
    (F : P ⟶ (streetNerveFinite 1).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite 1).map j)
    (hFB : lB ≫ F = (streetNerveFinite 1).map v) : KanLocal.Local F := by
  let Z := upward A
  let C := Aᶜ
  have hAZ : A ⊆ Z := fun x hx => ⟨x,hx,le_rfl⟩
  have hZ : IsUpperSet Z := by
    intro x y hxy hx
    obtain ⟨a,ha,hax⟩ := hx
    exact ⟨a,ha,hax.trans hxy⟩
  have hC : IsUpperSet C := isUpperSet_compl.mpr hA
  have hcov : Z ∪ C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl (hAZ hx)
    · exact Or.inr hx
  obtain ⟨YZ,jZ,vZ,uZ,scZ,hj,hv,sq⟩ :=
    attachment_nerve_cover 1 (by decide) A Z C hZ hC hAZ (disjoint_compl_right) hcov a j v sc
  let N := streetNerveFinite 1
  let e := N.map (sb 1 A Z hAZ)
  let b := N.map a
  let PZ := pushout b e
  let xZ := pushout.inl b e
  let zZ := pushout.inr b e
  let sZ := IsPushout.of_hasPushout b e
  let FZ : PZ ⟶ N.obj YZ := sZ.desc (N.map jZ) (N.map vZ) (by
    rw [← N.map_comp, ← N.map_comp, scZ.w])
  have hFZX : xZ ≫ FZ = N.map jZ := sZ.inl_desc _ _ _
  have hFZZ : zZ ≫ FZ = N.map vZ := sZ.inr_desc _ _ _
  obtain ⟨gZ,HZ,HYZ,hcoh⟩ := finite_poset_comparison_coherent
    (subposetMap A Z hAZ) r hr (fun z => (hadj (r z) z).mpr le_rfl)
    scZ sZ FZ hFZX hFZZ
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc 1 Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc 1 Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc 1 Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc 1 Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover 1 (by decide) Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb 1 (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := one_nerve_mono_orderMap
    (A := ↥(Z ∩ C)) (E := C) (subposetMap (Z ∩ C) C Set.inter_subset_right)
    (by intro x y he; exact Subtype.ext (congrArg (fun z : C => (z : B)) he))
  have hk : k ≫ FZ = N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb 1 (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc 1 C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc 1 C) ≫ lB) ≫ F = N.map (inc 1 C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_pushout_map k c FZ
    (KanLocal.local_heq FZ ⟨gZ, LastVertexProof.homotopic_of_homotopy HZ,
      LastVertexProof.homotopic_of_homotopy HYZ⟩) sp sq' F hFpZ hFC

end Thomason.AttachmentComparison

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalColimits
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits
open AttachmentComparison Attachments KanLocal

abbrev η (X : SSet.{u}) := (categorificationFiniteAdjunction 1).unit.app X

lemma unit_local_attachment {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {V W : SSet.{u}} (a : nerve A ⟶ V) (j : V ⟶ W) (v : nerve B ⟶ W)
    (sc : IsPushout a (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) j v)
    (hV : Local (η V)) : Local (η W) := by
  let i : nerve A ⟶ nerve B := nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have : Mono i := nerve_mono_orderMap
    (OrderHom.Subtype.val (fun element : B => element ∈ A)) Subtype.val_injective
  have : IsIso (η (nerve A)) := OneCat.oneUnitCatIso (Cat.of A)
  have : IsIso (η (nerve B)) := OneCat.oneUnitCatIso (Cat.of B)
  let b := N.map (C.map a)
  let c := N.map (C.map i)
  let P := pushout b c
  let lV := pushout.inl b c
  let lB := pushout.inr b c
  have ss : IsPushout b c lV lB := IsPushout.of_hasPushout b c
  have ss' : IsPushout (a ≫ η V) i lV (η (nerve B) ≫ lB) := by
    apply ss.of_iso (asIso (η (nerve A))).symm (Iso.refl _)
      (asIso (η (nerve B))).symm (Iso.refl _)
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, asIso_inv]
      apply (cancel_epi (η (nerve A))).mp
      simp [b]
    · simp only [Iso.symm_hom, asIso_inv]
      apply (cancel_epi (η (nerve A))).mp
      simp only [IsIso.hom_inv_id_assoc]
      apply (cancel_mono (η (nerve B))).mp
      simp [c]
    · simp
    · simp
  let q : W ⟶ P := sc.desc (η V ≫ lV) (η (nerve B) ≫ lB) (by
    simpa [Category.assoc] using ss'.w)
  have hqV : j ≫ q = η V ≫ lV := sc.inl_desc _ _ _
  have hqB : v ≫ q = η (nerve B) ≫ lB := sc.inr_desc _ _ _
  have hq : Local q := local_pushout_map a i (η V) hV sc ss' q hqV hqB
  have cs : IsPushout (C.map a) (inc 1 A) (C.map j) (C.map v) := sc.map C
  let t : P ⟶ N.obj (C.obj W) := ss.desc (N.map (C.map j)) (N.map (C.map v)) (by
    dsimp [b,c]
    rw [← N.map_comp, ← N.map_comp]
    exact congrArg N.map cs.w)
  have htV : lV ≫ t = N.map (C.map j) := ss.inl_desc _ _ _
  have htB : lB ≫ t = N.map (C.map v) := ss.inr_desc _ _ _
  have ht : Local t := comparison_local_one A hA r hr hadj (C.map a)
    (C.map j) (C.map v) cs ss t htV htB
  have hqt : q ≫ t = η W := by
    apply sc.hom_ext
    · rw [← Category.assoc,hqV,Category.assoc,htV]
      exact ((categorificationFiniteAdjunction 1).unit.naturality j).symm
    · rw [← Category.assoc,hqB,Category.assoc,htB]
      exact ((categorificationFiniteAdjunction 1).unit.naturality v).symm
  rw [← hqt]
  exact local_comp hq ht

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open KanLocal AttachmentComparison HornAttachments

lemma unit_local_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (hX : Local (η X)) :
    Local (η Y) := by
  have he : η Y = e.inv ≫ η X ≫ N.map (C.map e.hom) := by
    have hn : e.hom ≫ η Y = η X ≫ N.map (C.map e.hom) :=
      (categorificationFiniteAdjunction 1).unit.naturality e.hom
    rw [← hn]
    simp
  rw [he]
  exact local_comp (local_iso e.inv) (local_comp hX (local_iso _))

lemma unit_local_initial {X : SSet.{u}} (hX : IsInitial X) : Local (η X) := by
  let P := ULift.{u} Empty
  let : PartialOrder P := inferInstance
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  have : IsIso (η (nerve P)) := OneCat.oneUnitCatIso (Cat.of P)
  exact unit_local_of_iso (hP.uniqueUpToIso hX) (local_iso _)

lemma boundary_unit_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : Local (η (D.obj X))) :
    Local (η (D.obj Y)) ∧ Mono (D.map j) ∧ Mono (N.map (C.map (D.map j))) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hrA : ∀ a : A, rA ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
    PosetCoproduct.oldRetraction_retract I _ _ (flagRetraction_retract _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  have : Mono i := nerve_mono_orderMap
    (OrderHom.Subtype.val (fun element : PosetCoproduct.Piece I (Flags d) => element ∈ A))
    Subtype.val_injective
  refine ⟨unit_local_attachment A hA rA hrA hadj a' (D.map j) v' sq hX,
    Adhesive.mono_of_isPushout_of_mono_right sq, ?_⟩
  exact nerve_attachment_mono A hA (C.map a') (C.map (D.map j)) (C.map v') (sq.map C)

lemma unit_local_skeleton (K : SSet.{u}) (d : ℕ) :
    Local (η (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply unit_local_initial
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact (boundary_unit_successor
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
      ih).1

lemma skeleton_monos (K : SSet.{u}) (d : ℕ) :
    Mono (D.map ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))) ∧
      Mono (N.map (C.map (D.map
        ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))))) :=
  (boundary_unit_successor
    (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
    (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
    (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
    (unit_local_skeleton K d)).2

theorem unit_local_one (K : SSet.{u}) : Local (η (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D
  let G := c.F ⋙ D ⋙ C ⋙ N
  let f : F ⟶ G := Functor.whiskerLeft F (categorificationFiniteAdjunction 1).unit
  have hf : Local (colim.map f) := local_colimit_nat F G f
    (fun d => (skeleton_monos K d).1) (fun d => (skeleton_monos K d).2)
    (unit_local_skeleton K)
  have hcF : IsColimit (D.mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves D c.isColimit
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcG : IsColimit ((D ⋙ C ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ C ⋙ N) c.isColimit
  let eF : D.obj K ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj (C.obj (D.obj K)) ≅ colimit G :=
    hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have hF (d : ℕ) : D.map (c.incl.app d) ≫ eF.hom = colimit.ι F d :=
    hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) d
  have hG (d : ℕ) : colimit.ι G d ≫ eG.inv = N.map (C.map (D.map (c.incl.app d))) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit G) d
  have he : η (D.obj K) = eF.hom ≫ colim.map f ≫ eG.inv := by
    apply hcF.hom_ext
    intro d
    change D.map (c.incl.app d) ≫ η (D.obj K) =
      D.map (c.incl.app d) ≫ eF.hom ≫ colim.map f ≫ eG.inv
    rw [← Category.assoc, hF, ← Category.assoc, colimit.ι_map, Category.assoc, hG]
    exact (categorificationFiniteAdjunction 1).unit.naturality (D.map (c.incl.app d))
  rw [he]
  exact local_comp (local_iso _) (local_comp hf (local_iso _))

end Thomason.SubdividedUnit

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalReduction
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Reduction. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition.Posetal
open SubdividedUnit KanLocal LastVertexProof

theorem kan_poset_replacement (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ P : PartOrd.{u}, ∃ r : nerve P ⟶ K, Local r ∧ simplicialWeakEquivalences r := by
  obtain ⟨P,⟨e⟩⟩ := categorification_sdTwice_posetal K
  let E : N.obj (C.obj (D.obj K)) ≅ nerve P :=
    (oneNerveFunctorIso.app (C.obj (D.obj K))) ≪≫ nerveFunctor.mapIso e
  let l : D.obj K ⟶ K := Subdivision.lastVertex.app (SSet.sd.obj K) ≫
    Subdivision.lastVertex.app K
  have hl : Local l := local_comp (lastVertex_local _) (lastVertex_local _)
  obtain ⟨r,Hr⟩ := precomp_surjective (η (D.obj K)) (unit_local_one K) l
  have hr : Local r := local_of_precomp _ _ (unit_local_one K)
    (local_homotopic (homotopic_symm Hr) hl)
  have h : Local (E.inv ≫ r) := local_comp (local_iso _) hr
  exact ⟨P,E.inv ≫ r,h,local_weak _ h⟩
end Thomason.GeometricRecognition.Posetal

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma kan_local_heq {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (h : Local f) : IsHomotopyEquivalence f := by
  obtain ⟨g,hg⟩ := precomp_surjective f h (𝟙 A)
  refine ⟨g,hg,precomp_injective f h _ _ ?_⟩
  simpa only [Category.assoc,Category.comp_id,Category.id_comp] using homotopic_post hg f

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplicialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplicial Approximation. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

attribute [local instance] OAI.Thomason.GeometricRecognition.Contiguity.instDecidableEq_solutions
theorem homotopy_star_labels (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (H : C(unitInterval × PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ labels : unitInterval → level P n → Q,
      ∀ t s : unitInterval, dist t s < δ →
        ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
          labels s p ∈ (H (t,levelHomeomorph P n x)).weights.support := by
  let : MetricSpace (PolyPoint P) := embedding_weights.comapMetricSpace
    (fun x : PolyPoint P => (fun p => x.weights p))
  let U (q : Q) : Set (unitInterval × PolyPoint P) := {x | 0 < (H x).weights q}
  have hU (q : Q) : IsOpen (U q) := isOpen_lt continuous_const
    ((continuous_weights q).comp H.continuous)
  have hcover : (Set.univ : Set (unitInterval × PolyPoint P)) ⊆ ⋃ q, U q := by
    intro x hx
    obtain ⟨q,hq⟩ := (supportIndex (H x)).nonempty
    exact Set.mem_iUnion.mpr ⟨q,lt_of_le_of_ne ((H x).nonneg q)
      (Ne.symm (Finsupp.mem_support_iff.mp hq))⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  have hdim : ChainBound P (Fintype.card P + 1) := fun s =>
    (Finset.card_le_univ s.finset).trans (Nat.le_succ _)
  obtain ⟨n,e,he0,heδ,he⟩ := exists_small_mesh P coordinateVertex 2 (by norm_num)
    bound_coordinates (Nat.succ_pos _) hdim hδ
  have hv (t : unitInterval) (p : level P n) : ∃ q,
      Metric.ball (t,levelHomeomorph P n (vertex p)) δ ⊆ U q :=
    hLeb _ (Set.mem_univ _)
  choose labels hlabels using hv
  refine ⟨n,δ,hδ,labels,fun t s hts x p hp => ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply ne_of_gt
  apply hlabels s p
  change max (dist t s) (dist (fun q => (levelHomeomorph P n x).weights q)
    (fun q => (levelHomeomorph P n (vertex p)).weights q)) < δ
  apply max_lt hts
  rw [dist_eq_norm,coordinate_level,coordinate_level_vertex]
  exact (norm_evaluate_sub_le _ x _ e (fun q hq => he q p
    (x.chain.total hq hp))).trans_lt heδ

end Contiguity
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

attribute [local instance] OAI.Thomason.GeometricRecognition.Contiguity.instDecidableEq_solutions_1
lemma left_le_upper (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    orientedMap f.toFun f.chains s ≤ upperMap f g h s := by
  exact le_greatest (unionChain f g h s) _
    (Finset.mem_union_left _ (greatest_mem (imageChain f.toFun f.chains s)))
lemma right_le_upper (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    orientedMap g.toFun g.chains s ≤ upperMap f g h s := by
  exact le_greatest (unionChain f g h s) _
    (Finset.mem_union_right _ (greatest_mem (imageChain g.toFun g.chains s)))

lemma orientedMap_monotone (f : P →o Q) (s : NonemptyFiniteChains P) :
    orientedMap f (preservesChains_monotone f) s = f (greatest s) := by
  apply le_antisymm
  · obtain ⟨p,hp,he⟩ := orientedMap_mem f (preservesChains_monotone f) s
    rw [he]
    exact f.monotone (le_greatest s p hp)
  · exact le_greatest (imageChain f (preservesChains_monotone f) s) _
      (Finset.mem_image.mpr ⟨greatest s,greatest_mem s,rfl⟩)

end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

namespace Thomason.TopologicalHorn

lemma anodyne_realization_retract {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    ∃ r : SSet.toTop.obj B ⟶ SSet.toTop.obj A,
      SSet.toTop.map i ≫ r = 𝟙 _ ∧
      (SSet.toTop.map i ≫ r ≫ SSet.toTop.map i).hom = (SSet.toTop.map i).hom ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((SSet.toTop.map i).hom.comp r.hom) (ContinuousMap.id _)
        (Set.range (SSet.toTop.map i))) := by
  let j := SSet.toTop.map i
  obtain ⟨r,hr⟩ := anodyne_top_extension i hi (SSet.toTop.obj A) (𝟙 _)
  have hre (a : SSet.toTop.obj A) : r (j a) = a := ConcreteCategory.congr_hom hr a
  let f : SSet.toTop.obj A ⟶ PathSpace (SSet.toTop.obj B) :=
    TopCat.ofHom (ContinuousMap.const'.comp j.hom)
  let g : SSet.toTop.obj B ⟶ EndpointSpace (SSet.toTop.obj B) :=
    TopCat.ofHom ⟨fun b => (j (r b),b), (j.hom.continuous.comp r.hom.continuous).prodMk continuous_id⟩
  have sq : CommSq f j (pathEndpoints (SSet.toTop.obj B)) g := by
    constructor
    apply ConcreteCategory.hom_ext
    intro a
    change (j a,j a) = (j (r (j a)),j a)
    rw [hre]
  let : HasLiftingProperty j (pathEndpoints (SSet.toTop.obj B)) :=
    (sSetTopAdj.hasLiftingProperty_iff i _).mpr (hi _ (singular_path_fibration _))
  have hzero (b : SSet.toTop.obj B) : sq.lift b 0 = j (r b) :=
    congrArg Prod.fst (ConcreteCategory.congr_hom sq.fac_right b)
  have hone (b : SSet.toTop.obj B) : sq.lift b 1 = b :=
    congrArg Prod.snd (ConcreteCategory.congr_hom sq.fac_right b)
  have hfixed (a : SSet.toTop.obj A) (t : I) : sq.lift (j a) t = j a :=
    congrArg (fun γ : C(I,SSet.toTop.obj B) => γ t) (ConcreteCategory.congr_hom sq.fac_left a)
  refine ⟨r,hr,by simp only [← Category.assoc,hr,Category.id_comp],?_⟩
  refine ⟨{ toHomotopy :=
    { toFun := fun q => sq.lift q.2 q.1
      continuous_toFun := ?_
      map_zero_left := hzero
      map_one_left := hone }
            prop' := ?_ }⟩
  · exact continuous_eval.comp ((sq.lift.hom.continuous.comp continuous_snd).prodMk continuous_fst)
  · rintro t b ⟨a,rfl⟩
    change sq.lift (j a) t = j (r (j a))
    rw [hre]
    exact hfixed a t

end Thomason.TopologicalHorn

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeContiguity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFixedDecidableEq_r2f8ca6_1 : DecidableEq Q := Classical.decEq Q
def relativeVertices (P : PartOrd.{u}) (A : Set (PolyPoint P)) (n : ℕ) :
    Set (level P n) := {p | levelHomeomorph P n (vertex p) ∈ A}

theorem homotopy_relative_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (H : C(unitInterval × PolyPoint P, PolyPoint Q))
    (A : Set (PolyPoint P)) (q : Q) (hA : ∀ t x, x ∈ A → H (t,x) = vertex q) :
    ∃ n : ℕ, ∃ f g : ChainMap (level P n) Q,
      RelativeRelated (relativeVertices P A n) q f g ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        f p ∈ (H (0,levelHomeomorph P n x)).weights.support) ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        g p ∈ (H (1,levelHomeomorph P n x)).weights.support) := by
  obtain ⟨n,δ,hδ,labels,hl⟩ := homotopy_star_labels P H
  have hs (t : unitInterval) := hl t t (by simpa using hδ)
  let f (t : unitInterval) : ChainMap (level P n) Q :=
    ⟨labels t,labels_preserve_chains P (fun x => H (t,x)) n (labels t) (hs t)⟩
  have fixed (t : unitInterval) : Fixed (relativeVertices P A n) q (f t) :=
    fixed_of_carrier _ q (f t) _ (hs t) (fun p hp => hA t _ hp)
  let fr (t : unitInterval) : FixedMap (relativeVertices P A n) q := ⟨f t,fixed t⟩
  let F (t : unitInterval) : Quotient (fixedMapSetoid (relativeVertices P A n) q) :=
    Quotient.mk _ (fr t)
  have hF : IsLocallyConstant F := by
    intro B
    rw [Metric.isOpen_iff]
    intro t ht
    refine ⟨δ,hδ,fun s hst => ?_⟩
    have he : F s = F t := Quotient.sound (Relation.EqvGen.rel _ _
      (show FixedContiguous (fr s) (fr t) from
        contiguous_of_carrier (f s) (f t) (fun x => H (t,levelHomeomorph P n x))
          (hl t s (by simpa only [Metric.mem_ball,dist_comm] using hst)) (hs t)))
    change F s ∈ B
    rw [he]
    exact ht
  have h01 : F 0 = F 1 := congrFun (hF.eq_const 1) 0
  exact ⟨n,f 0,f 1,⟨fixed 0,fixed 1,Quotient.exact h01⟩,hs 0,hs 1⟩

theorem homotopy_relative_subdivision_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f g : P →o Q)
    (H : (affineMap f).Homotopy (affineMap g))
    (A : Set (PolyPoint P)) (q : Q) (hA : ∀ t x, x ∈ A → H (t,x) = vertex q) :
    ∃ n : ℕ, RelativeRelated (relativeVertices P A n) q
      (toChainMap (f.comp (last P n))) (toChainMap (g.comp (last P n))) := by
  obtain ⟨n,a,b,⟨ha',hb',hab⟩,ha,hb⟩ := homotopy_relative_contiguity P H.toContinuousMap A q hA
  have hf (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (f.comp (last P n)) p ∈
        (H (0,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_zero]
    exact map_support_image f (preservesChains_monotone f) _ _ (last_support P n x p hp)
  have hg (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (g.comp (last P n)) p ∈
        (H (1,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_one]
    exact map_support_image g (preservesChains_monotone g) _ _ (last_support P n x p hp)
  have hfr := fixed_of_carrier (relativeVertices P A n) q _ _ hf (fun p hp => hA 0 _ hp)
  have hgr := fixed_of_carrier (relativeVertices P A n) q _ _ hg (fun p hp => hA 1 _ hp)
  refine ⟨n,hfr,hgr,Relation.EqvGen.trans _ (⟨a,ha'⟩ : FixedMap _ q) _ ?_
    (Relation.EqvGen.trans _ (⟨b,hb'⟩ : FixedMap _ q) _ hab ?_)⟩
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier _ a _ hf ha)
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier b _ _ hb hg)
end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFaceDecidableEq_r2f8ca6_1 : DecidableEq Q := Classical.decEq Q
lemma oriented_fixed (B : Set P) (q : Q) (f : ChainMap P Q) (hf : Fixed B q f)
    (s : relativeFaceSet B) : orientedMap f.toFun f.chains s.val = q := by
  obtain ⟨p,hp,he⟩ := orientedMap_mem f.toFun f.chains s.val
  exact he.trans (hf p (s.property p hp))

lemma fixed_contiguous_nerve (B : Set P) (q : Q) (f g : FixedMap B q)
    (h : FixedContiguous f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.val.toFun f.val.chains).toFunctor)
      (nerveMap (orientedMap g.val.toFun g.val.chains).toFunctor) := by
  refine Relation.EqvGen.trans _ (nerveMap (upperMap f.val g.val h).toFunctor) _ ?_ ?_
  · apply Relation.EqvGen.rel
    exact ⟨HornSubdivision.orderHomotopy _ _ (left_le_upper f.val g.val h),
      orderHomotopy_fixed _ _ _ _ q (oriented_fixed B q f.val f.property)
        (upper_fixed B q f.val g.val h f.property g.property)⟩
  · apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact ⟨HornSubdivision.orderHomotopy _ _ (right_le_upper f.val g.val h),
      orderHomotopy_fixed _ _ _ _ q (oriented_fixed B q g.val g.property)
        (upper_fixed B q f.val g.val h f.property g.property)⟩

lemma fixed_related_nerve (B : Set P) (q : Q) (f g : FixedMap B q)
    (h : Relation.EqvGen FixedContiguous f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.val.toFun f.val.chains).toFunctor)
      (nerveMap (orientedMap g.val.toFun g.val.chains).toFunctor) := by
  induction h with
  | rel f g h => exact fixed_contiguous_nerve B q f g h
  | refl f => exact Relation.EqvGen.refl _
  | symm f g h ih => exact Relation.EqvGen.symm _ _ ih
  | trans f g h hfg hgh ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

lemma relative_related_nerve (B : Set P) (q : Q) (f g : ChainMap P Q)
    (h : RelativeRelated B q f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.toFun f.chains).toFunctor)
      (nerveMap (orientedMap g.toFun g.chains).toFunctor) := by
  obtain ⟨hf,hg,h⟩ := h
  exact fixed_related_nerve B q ⟨f,hf⟩ ⟨g,hg⟩ h
end Thomason.GeometricRecognition.Contiguity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision

lemma stage_unmate_relative {A B X : SSet.{u}} (i : B ⟶ A) [Mono i] (n : ℕ)
    (t : A ⟶ exStage X (n+1)) (k : B ⟶ exStage X n)
    (ht : i ≫ t = k ≫ exComparison.app (exStage X n)) :
    ∃ G : SSet.Homotopy (lastVertex.app A ≫ t ≫ exInfinityInclusion X (n+1))
      ((SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t ≫ exInfinityInclusion X n),
      SSet.sd.map i ▷ Δ[1] ≫ G.h =
        fst (SSet.sd.obj B) Δ[1] ≫ lastVertex.app B ≫ k ≫ exInfinityInclusion X n := by
  let E := exInfinity X
  let : SSet.KanComplex E := exInfinity_kan X
  let : SSet.KanComplex (SSet.ex.obj E) := ex_kan E
  obtain ⟨H,hH⟩ := homotopy_of_anodyne_eq_relative (exComparison.app (exStage X n))
    (exComparison_anodyne _) (exInfinityInclusion X (n+1) ≫ exComparison.app E)
    (SSet.ex.map (exInfinityInclusion X n)) (by
      rw [← Category.assoc,exInfinityInclusion_step]
      exact exComparison.naturality (exInfinityInclusion X n))
  let F := homotopy_pre t H
  have hF : i ▷ Δ[1] ≫ F.h = fst B Δ[1] ≫ i ≫ t ≫ SSet.ex.map (exInfinityInclusion X n) := by
    change i ▷ Δ[1] ≫ t ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,ht,comp_whiskerRight_assoc,hH]
    change k ▷ Δ[1] ≫ fst (exStage X n) Δ[1] ≫ _ = _
    rw [whiskerRight_fst_assoc]
    rw [← Category.assoc (exComparison.app _) (exInfinityInclusion X (n+1)),
      exInfinityInclusion_step,← Category.assoc i t,ht]
    simp only [Category.assoc]
    rw [← exComparison.naturality]
    rfl
  obtain ⟨G,hG⟩ := unmate_homotopy_relative i F hF
  have hf : (SSet.sdExAdjunction.homEquiv A E).symm
      (t ≫ exInfinityInclusion X (n+1) ≫ exComparison.app E) =
      lastVertex.app A ≫ t ≫ exInfinityInclusion X (n+1) := by
    rw [← Category.assoc,← mate_lastVertex,Equiv.symm_apply_apply]
  have hg : (SSet.sdExAdjunction.homEquiv A E).symm
      (t ≫ SSet.ex.map (exInfinityInclusion X n)) =
      (SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t ≫ exInfinityInclusion X n :=
    SSet.sdExAdjunction.homEquiv_naturality_right_symm t (exInfinityInclusion X n)
  let G' := CoherentGluing.toHomotopy G.h (G.h₀.trans hf) (G.h₁.trans hg)
  refine ⟨G',?_⟩
  change SSet.sd.map i ▷ Δ[1] ≫ G.h = _
  rw [hG,hg,← Category.assoc (SSet.sd.map i),stage_unmate_boundary i n t k ht]
  simp only [Category.assoc]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma sdNerve_inv_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    nerveMap (NonemptyFiniteChains.orderHomMap f).toFunctor ≫ (sdNerveIso (E := Q)).inv =
      (sdNerveIso (E := P)).inv ≫ SSet.sd.map (nerveMap f.toFunctor) := by
  apply (cancel_mono (sdNerveIso (E := Q)).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hh := sdNerveMap_naturality f
  change SSet.sd.map (nerveMap f.toFunctor) ≫ (sdNerveIso (E := Q)).hom =
    (sdNerveIso (E := P)).hom ≫ nerveMap (NonemptyFiniteChains.orderHomMap f).toFunctor at hh
  rw [hh,Iso.inv_hom_id_assoc]

lemma sdNerve_inv_last (P : PartOrd.{u}) :
    (sdNerveIso (E := P)).inv ≫ lastVertex.app (nerve P) = nerveMap (chainLast (X := P)).toFunctor := by
  rw [← lastVertex_nerve]
  change (sdNerveIso (E := P)).inv ≫ (sdNerveIso (E := P)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

lemma chainLast_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    (chainLast (X := Q)).comp (NonemptyFiniteChains.orderHomMap f) =
      f.comp (chainLast (X := P)) := by
  have hc {T : Type u} [PartialOrder T] (s : NonemptyFiniteChains T) :
      chainLast s = greatest s := by
    apply le_antisymm
    · exact le_greatest s _ (chainGreatest_mem s)
    · exact (chain_has_greatest s).choose_spec.2 _ (greatest_mem s)
  ext s
  change chainLast (s.map f) = f (chainLast s)
  rw [hc,hc,greatest_map]

attribute [instance] PairRefinement.finiteR PairRefinement.finiteS

def PairRefinement.prepend (P B : PartOrd.{u}) (i : B →o P)
    (hi : Function.Injective i)
    (d : PairRefinement (PartOrd.of (NonemptyFiniteChains P))
      (PartOrd.of (NonemptyFiniteChains B)) (NonemptyFiniteChains.orderHomMap i)) :
    PairRefinement P B i where
  R := d.R
  S := d.S
  finiteR := d.finiteR
  finiteS := d.finiteS
  j := d.j
  injective := d.injective
  l := (chainLast (X := P)).comp d.l
  k := (chainLast (X := B)).comp d.k
  square := by
    rw [OrderHom.comp_assoc,d.square,← OrderHom.comp_assoc,chainLast_natural,OrderHom.comp_assoc]
  local_l := by rw [nerveOrderMap_comp]; exact local_comp d.local_l (chainLast_local P)
  local_k := by rw [nerveOrderMap_comp]; exact local_comp d.local_k (chainLast_local B)
  home := d.home.trans subdivisionHomeomorph
  homeB := d.homeB.trans subdivisionHomeomorph
  natural := by
    intro x
    change subdivide (d.home (map d.j (preservesChains_monotone d.j) x)) = _
    rw [d.natural,subdivide_natural i hi]
    rfl

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma stage_order_pair_representative (Q : PartOrd.{u}) (q : Q) (n : ℕ) :
    ∀ (P B : PartOrd.{u}) [Finite P] [Finite B] (i : B →o P), Function.Injective i →
      ∀ (t : nerve P ⟶ exStage (nerve Q) n),
      nerveMap i.toFunctor ≫ t = nerveMap (constantOrder B q).toFunctor ≫
        (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n)) →
    ∃ d : PairRefinement P B i, ∃ b : d.R →o Q,
      b.comp d.j = constantOrder d.S q ∧
      BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q))
        (nerveMap d.l.toFunctor ≫ t ≫ exInfinityInclusion (nerve Q) n)
        (nerveMap b.toFunctor ≫ exInfinityComparison (nerve Q)) := by
  induction n with
  | zero =>
    intro P B hP hB i hi t ht
    obtain ⟨b,hb⟩ := orderMap_of_nerve t
    have hbc : b.comp i = constantOrder B q := by
      have ht' : nerveMap i.toFunctor ≫ t = nerveMap (constantOrder B q).toFunctor := by
        have h0 : (exSequence (nerve Q)).map (homOfLE (Nat.zero_le 0)) = 𝟙 (nerve Q) :=
          (exSequence (nerve Q)).map_id 0
        rw [h0] at ht
        exact ht.trans (Category.comp_id _)
      ext x
      have hh := congrArg (fun f : nerve B ⟶ nerve Q =>
        ((f.app (Opposite.op ⦋0⦌)) ((CategoryTheory.Functor.const (Fin 1)).obj x)).obj 0)
        (show nerveMap i.toFunctor ≫ nerveMap b.toFunctor = nerveMap (constantOrder B q).toFunctor from by simpa only [hb] using ht')
      exact hh
    refine ⟨PairRefinement.identity P B i hi,b,hbc,?_⟩
    change BasedHomotopy (nerveMap i.toFunctor) _
      (nerveMap (OrderHom.id : P →o P).toFunctor ≫ t ≫ _) _
    rw [nerveOrderMap_id,Category.id_comp,← hb]
    apply based_homotopy_refl
    rw [← Category.assoc,← nerveOrderMap_comp,hbc]
    rfl
  | succ n ih =>
    intro P B hP hB i hi t ht
    let F := PartOrd.of (NonemptyFiniteChains P)
    let G := PartOrd.of (NonemptyFiniteChains B)
    let j : G →o F := NonemptyFiniteChains.orderHomMap i
    let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
    let zeroInclusion : nerve Q ⟶ exStage (nerve Q) n :=
      (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n))
    have zeroInclusion_eq : zeroInclusion ≫ exInfinityInclusion (nerve Q) n =
        exInfinityComparison (nerve Q) := exSequence_zero_inclusion (nerve Q) n
    let k : nerve B ⟶ exStage (nerve Q) n :=
      nerveMap (constantOrder B q).toFunctor ≫ zeroInclusion
    have ht' : nerveMap i.toFunctor ≫ t = k ≫ exComparison.app (exStage (nerve Q) n) := by
      rw [ht,exSequence_zero_succ]
      exact (Category.assoc (nerveMap (constantOrder B q).toFunctor) zeroInclusion
        (exComparison.app (exStage (nerve Q) n))).symm
    let t' := (sdNerveIso (E := P)).inv ≫
      (SSet.sdExAdjunction.homEquiv (nerve P) (exStage (nerve Q) n)).symm t
    have ht'' : nerveMap j.toFunctor ≫ t' = nerveMap (constantOrder G q).toFunctor ≫
        (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n)) := by
      change nerveMap j.toFunctor ≫ t' = nerveMap (constantOrder G q).toFunctor ≫ zeroInclusion
      dsimp only [t',j]
      rw [← Category.assoc,sdNerve_inv_natural,Category.assoc,
        stage_unmate_boundary _ n t k ht',← Category.assoc,sdNerve_inv_last]
      dsimp only [k]
      rw [nerve_constant_pre'_assoc]
    obtain ⟨d,b,hb,Hb⟩ := ih F G j (chains_map_injective i hi) t' ht''
    let D := PairRefinement.prepend P B i hi d
    let : SSet.KanComplex (exInfinity (nerve Q)) := exInfinity_kan _
    let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
    refine ⟨D,b,hb,?_⟩
    obtain ⟨H,hH⟩ := stage_unmate_relative (nerveMap i.toFunctor) n t k ht'
    have HH : BasedHomotopy (SSet.sd.map (nerveMap i.toFunctor))
        (lastVertex.app (nerve B) ≫ k ≫ exInfinityInclusion (nerve Q) n)
        (lastVertex.app (nerve P) ≫ t ≫ exInfinityInclusion (nerve Q) (n+1))
        ((SSet.sdExAdjunction.homEquiv (nerve P) (exStage (nerve Q) n)).symm t ≫
          exInfinityInclusion (nerve Q) n) := ⟨H,hH⟩
    have H₀ := based_homotopy_pre _ (nerveMap j.toFunctor) (sdNerveIso (E := P)).inv
      (sdNerveIso (E := B)).inv (sdNerve_inv_natural i) _ HH
    simp only [← Category.assoc (sdNerveIso (E := P)).inv,
      ← Category.assoc (sdNerveIso (E := B)).inv,sdNerve_inv_last] at H₀
    have H₁ := based_homotopy_pre _ (nerveMap d.j.toFunctor)
      (nerveMap d.l.toFunctor) (nerveMap d.k.toFunctor)
      (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square]) _ H₀
    have hz : nerveMap d.k.toFunctor ≫ (nerveMap (chainLast (X := B)).toFunctor ≫
        k ≫ exInfinityInclusion (nerve Q) n) =
        nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q) := by
      dsimp only [k]
      simp only [Category.assoc,nerve_constant_pre'_assoc,zeroInclusion_eq]
    rw [hz] at H₁
    have HH' : BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q))
        (nerveMap ((chainLast (X := P)).comp d.l).toFunctor ≫
          t ≫ exInfinityInclusion (nerve Q) (n+1))
        (nerveMap d.l.toFunctor ≫ t' ≫ exInfinityInclusion (nerve Q) n) := by
      rw [nerveOrderMap_comp]
      simpa only [Category.assoc,t'] using H₁
    exact based_homotopy_trans (nerveMap d.j.toFunctor) _ HH' Hb

lemma finite_pair_order_representative {K : SSet.{u}} [SSet.KanComplex K]
    (Q : PartOrd.{u}) (q : Q) (r : nerve Q ⟶ K) (e : exInfinity (nerve Q) ⟶ K)
    (he : IsHomotopyEquivalence e) (hre : exInfinityComparison (nerve Q) ≫ e = r)
    (P B : PartOrd.{u}) [Finite P] [Finite B] (i : B →o P) (hi : Function.Injective i)
    (a : nerve P ⟶ K)
    (ha : nerveMap i.toFunctor ≫ a = nerveMap (constantOrder B q).toFunctor ≫ r) :
    ∃ d : PairRefinement P B i, ∃ b : d.R →o Q,
      b.comp d.j = constantOrder d.S q ∧
      BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ r)
        (nerveMap d.l.toFunctor ≫ a) (nerveMap b.toFunctor ≫ r) := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : SSet.KanComplex (exInfinity (nerve Q)) := exInfinity_kan _
  obtain ⟨g,H,hg,hH⟩ := relative_representative e he (nerveMap i.toFunctor)
    (nerveMap (constantOrder B q).toFunctor ≫ exInfinityComparison (nerve Q)) a
    (by simpa only [Category.assoc,hre] using ha)
  obtain ⟨n,t,ht,ht'⟩ := finite_relative_stage (nerveMap i.toFunctor)
    (nerveMap (constantOrder B q).toFunctor) g hg
  obtain ⟨d,b,hb,Hb⟩ := stage_order_pair_representative Q q n P B i hi t ht'
  let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
  have H₀ : BasedHomotopy (nerveMap i.toFunctor)
      (nerveMap (constantOrder B q).toFunctor ≫ r) (g ≫ e) a :=
    ⟨H,by simpa only [Category.assoc,hre] using hH⟩
  have H₁ := based_homotopy_pre _ (nerveMap d.j.toFunctor)
    (nerveMap d.l.toFunctor) (nerveMap d.k.toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square]) _ H₀
  simp only [nerve_constant_pre'_assoc] at H₁
  have H₂ := based_homotopy_post _ _ Hb e
  simp only [Category.assoc,hre,ht] at H₂
  exact ⟨d,b,hb,based_homotopy_trans _ _ (based_homotopy_symm _ _ H₁) H₂⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity HornSubdivision

lemma nerve_constant_vertex {Q B : Type u} [PartialOrder Q] [PartialOrder B]
    (v : (nerve Q) _⦋0⦌) :
    nerveMap (constantOrder B (v.obj 0)).toFunctor = SSet.const v := by
  ext n a j
  rfl

lemma pointed_kan_poset_replacement (K : SSet.{u}) [SSet.KanComplex K] (x : K _⦋0⦌) :
    ∃ Q : PartOrd.{u}, ∃ q : Q, ∃ r : nerve Q ⟶ K,
      Local r ∧ simplicialWeakEquivalences r ∧
      (∀ (B : Type u) [PartialOrder B], nerveMap (constantOrder B q).toFunctor ≫ r = SSet.const x) := by
  obtain ⟨Q,r,hr,hw⟩ := Posetal.kan_poset_replacement K
  obtain ⟨v,hv⟩ := (KanQuillen.map_components_bijective_of_weak r hw).2 (SSet.π₀.mk x)
  obtain ⟨v,rfl⟩ := SSet.π₀.mk_surjective v
  have h : SSet.π₀.mk (r.app _ v) = SSet.π₀.mk x := hv
  let i := SSet.const (X := Δ[0]) v
  let : Mono i := point_mono v
  obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const h)
  have H' : SSet.Homotopy (i ≫ r) (SSet.const x) := by
    simpa only [i,SSet.const_comp] using H
  obtain ⟨s,G,hs,_⟩ := homotopy_extension i r H'
  have hrs : Homotopic r s := Relation.EqvGen.rel _ _ ⟨G⟩
  have hlocal : Local s := local_homotopic hrs hr
  have hsx : s.app _ v = x := by
    have hh := congrArg SSet.yonedaEquiv hs
    simpa only [i,SSet.const_comp,SSet.yonedaEquiv_const] using hh
  refine ⟨Q,v.obj 0,s,hlocal,local_weak s hlocal,?_⟩
  intro B hB
  rw [nerve_constant_vertex,SSet.const_comp,hsx]

lemma pointed_kan_ex_replacement (K : SSet.{u}) [SSet.KanComplex K] (x : K _⦋0⦌) :
    ∃ Q : PartOrd.{u}, ∃ q : Q, ∃ r : nerve Q ⟶ K, ∃ e : Subdivision.exInfinity (nerve Q) ⟶ K,
      Subdivision.exInfinityComparison (nerve Q) ≫ e = r ∧
      simplicialWeakEquivalences r ∧ IsHomotopyEquivalence e ∧
      (∀ (B : Type u) [PartialOrder B], nerveMap (constantOrder B q).toFunctor ≫ r = SSet.const x) := by
  obtain ⟨Q,q,r,hr,hw,hx⟩ := pointed_kan_poset_replacement K x
  obtain ⟨e,he⟩ := extend_anodyne (Subdivision.exInfinityComparison (nerve Q))
    (Subdivision.exInfinityComparison_anodyne _) r
  have : SSet.KanComplex (Subdivision.exInfinity (nerve Q)) := Subdivision.exInfinity_kan _
  exact ⟨Q,q,r,e,he,hw,kan_local_heq e (local_of_precomp _ _
    (local_anodyne _ (Subdivision.exInfinityComparison_anodyne _)) (he.symm ▸ hr)),hx⟩
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Geometry. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal

lemma realization_homotopy_rel {A B K : SSet.{u}} (i : B ⟶ A) [Mono i]
    {f g : A ⟶ K} (H : SSet.Homotopy f g)
    (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ i ≫ g) :
    Nonempty ((SSet.toTop.map f).hom.HomotopyRel (SSet.toTop.map g).hom
      (Set.range (SSet.toTop.map i))) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hinl : s.inl ≫ s.ι = A ◁ SSet.stdSimplex.δ (n := 0) 0 := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have heq : s.ι ≫ H.h = s.ι ≫ fst A Δ[1] ≫ g := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,hinl,← Category.assoc,hinl]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      rw [← Category.assoc,CoherentGluing.zeroFactor_one,H.h₁,
        ← Category.assoc,CoherentGluing.zeroFactor_one,SSet.ι₁_fst_assoc]
    · rw [← Category.assoc,hinr,← Category.assoc,hinr,hH,
        whiskerRight_fst_assoc]
  obtain ⟨r,hr,_,⟨R⟩⟩ := TopologicalHorn.anodyne_realization_retract s.ι
    (SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0))
  let j := SSet.toTop.map s.ι
  let e := SSet.toTop.map (SSet.ι₀ (X := A))
  let z : C(SSet.toTop.obj A,SSet.toTop.obj (A ⊗ Δ[1])) := j.hom.comp (r.hom.comp e.hom)
  have hz (b : SSet.toTop.obj B) : e (SSet.toTop.map i b) ∈ Set.range j := by
    refine ⟨SSet.toTop.map (SSet.ι₀ ≫ s.inr) b,?_⟩
    change (SSet.toTop.map (SSet.ι₀ ≫ s.inr) ≫ j) b = _
    dsimp only [j,e]
    rw [← Functor.map_comp,Category.assoc,hinr,SSet.ι₀_comp,Functor.map_comp]
    rfl
  let h : z.HomotopyRel e.hom (Set.range (SSet.toTop.map i)) :=
    { toHomotopy := R.toHomotopy.compContinuousMap e.hom
      prop' := by
        rintro t a ⟨b,rfl⟩
        exact R.prop t _ (hz b) }
  let h₁ := h.compContinuousMap (SSet.toTop.map H.h).hom
  let h₂ := h.compContinuousMap (SSet.toTop.map (fst A Δ[1] ≫ g)).hom
  have hstart : (SSet.toTop.map H.h).hom.comp z =
      (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp z := by
    have hh : (SSet.toTop.map H.h).hom.comp j.hom =
        (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp j.hom := by
      change (SSet.toTop.map s.ι ≫ SSet.toTop.map H.h).hom =
        (SSet.toTop.map s.ι ≫ SSet.toTop.map (fst A Δ[1] ≫ g)).hom
      rw [← Functor.map_comp,← Functor.map_comp,heq]
    simpa only [z,← ContinuousMap.comp_assoc] using
      congrArg (fun q : C(SSet.toTop.obj s.pt,SSet.toTop.obj K) =>
        q.comp (r.hom.comp e.hom)) hh
  have hf : (SSet.toTop.map H.h).hom.comp e.hom = (SSet.toTop.map f).hom := by
    change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map H.h).hom = _
    rw [← Functor.map_comp,H.h₀]
  have hg : (SSet.toTop.map (fst A Δ[1] ≫ g)).hom.comp e.hom = (SSet.toTop.map g).hom := by
    change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map (fst A Δ[1] ≫ g)).hom = _
    rw [← Functor.map_comp,SSet.ι₀_fst_assoc]
  exact ⟨(h₁.cast rfl hf).symm.trans (h₂.cast hstart.symm hg)⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma pair_relative_nerve_detection (P B : PartOrd.{u}) [Finite P]
    (i : B →o P) (hi : Function.Injective i) {Q : Type u} [PartialOrder Q]
    (q : Q) (f g : P →o Q) (H : (affineMap f).Homotopy (affineMap g))
    (hH : ∀ (t : unitInterval) (x : PolyPoint B), H (t,map i (preservesChains_monotone i) x) = vertex q) :
    ∃ n, BasedRelated (nerveMap (levelMap i n).toFunctor)
      (nerveMap (constantOrder (level B n) q).toFunctor)
      (nerveMap (f.comp (last P n)).toFunctor)
      (nerveMap (g.comp (last P n)).toFunctor) := by
  let : Fintype P := Fintype.ofFinite P
  let A : Set (PolyPoint P) := Set.range (map i (preservesChains_monotone i))
  have hA : ∀ t x, x ∈ A → H (t,x) = vertex q := by
    rintro t x ⟨y,rfl⟩
    exact hH t y
  obtain ⟨n,hn⟩ := homotopy_relative_subdivision_contiguity P f g H A q hA
  let c : level B (n+1) →o relativeFaceSet (relativeVertices P A n) :=
    { toFun := fun s => ⟨s.map (levelMap i n),by
        intro p hp
        obtain ⟨x,hx,rfl⟩ := (NonemptyFiniteChains.mem_map_iff s (levelMap i n) p).mp hp
        change levelHomeomorph P n (vertex (levelMap i n x)) ∈ A
        refine ⟨levelHomeomorph B n (vertex x),?_⟩
        rw [← map_vertex (levelMap i n) (preservesChains_monotone (levelMap i n)),
          levelHomeomorph_natural i hi]⟩
      monotone' := fun _ _ h => (NonemptyFiniteChains.orderHomMap (levelMap i n)).monotone h }
  have hw : nerveMap (levelMap i (n+1)).toFunctor ≫ 𝟙 _ =
      nerveMap c.toFunctor ≫ nerveMap (relativeFaceInclusion (relativeVertices P A n)).toFunctor := by
    rw [Category.comp_id,← nerveOrderMap_comp]
    rfl
  have hn' := based_related_pre _ (nerveMap (levelMap i (n+1)).toFunctor) (𝟙 _)
    (nerveMap c.toFunctor) hw _ (relative_related_nerve (relativeVertices P A n) q _ _ hn)
  have hf : orientedMap (toChainMap (f.comp (last P n))).toFun
      (toChainMap (f.comp (last P n))).chains = f.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (f.comp (last P n)) s
  have hg : orientedMap (toChainMap (g.comp (last P n))).toFun
      (toChainMap (g.comp (last P n))).chains = g.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (g.comp (last P n)) s
  refine ⟨n+1,?_⟩
  simpa only [hf,hg,Category.id_comp,nerve_constant_pre'] using hn'

lemma pair_relative_nerve_descent (P B : PartOrd.{u}) [Finite P]
    (i : B →o P) (hi : Function.Injective i) {Q : Type u} [PartialOrder Q]
    (q : Q) (f g : P →o Q) (hf : f.comp i = constantOrder B q)
    (hg : g.comp i = constantOrder B q)
    (H : (affineMap f).Homotopy (affineMap g))
    (hH : ∀ (t : unitInterval) (x : PolyPoint B),
      H (t,map i (preservesChains_monotone i) x) = vertex q)
    (K : SSet.{u}) [SSet.KanComplex K] (r : nerve Q ⟶ K) :
    BasedHomotopy (nerveMap i.toFunctor) (nerveMap (constantOrder B q).toFunctor ≫ r)
      (nerveMap f.toFunctor ≫ r) (nerveMap g.toFunctor ≫ r) := by
  obtain ⟨n,hn⟩ := pair_relative_nerve_detection P B i hi q f g H hH
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : Mono (nerveMap (levelMap i n).toFunctor) :=
    nerveOrderMap_mono _ (levelMap_injective i hi n)
  have hfr : nerveMap i.toFunctor ≫ nerveMap f.toFunctor ≫ r =
      nerveMap (constantOrder B q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,hf]
  have hgr : nerveMap i.toFunctor ≫ nerveMap g.toFunctor ≫ r =
      nerveMap (constantOrder B q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,hg]
  have hb : nerveMap (levelMap i n).toFunctor ≫ nerveMap (f.comp (last P n)).toFunctor ≫ r =
      nerveMap (constantOrder (level B n) q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,OrderHom.comp_assoc,last_natural,
      ← OrderHom.comp_assoc,hf,constantOrder_comp]
  obtain ⟨G,hG⟩ := based_related_homotopy _ _ (based_related_post _ _ hn r) hb
  let G' : SSet.Homotopy (nerveMap (last P n).toFunctor ≫ nerveMap f.toFunctor ≫ r)
      (nerveMap (last P n).toFunctor ≫ nerveMap g.toFunctor ≫ r) :=
    CoherentGluing.toHomotopy G.h
      (by simpa only [nerveOrderMap_comp,Category.assoc] using G.h₀)
      (by simpa only [nerveOrderMap_comp,Category.assoc] using G.h₁)
  refine pair_local_injective_plain (nerveMap i.toFunctor)
    (nerveMap (levelMap i n).toFunctor) (nerveMap (last P n).toFunctor)
    (nerveMap (last B n).toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,last_natural])
    (last_local P n) (last_local B n) _ _ _ hfr hgr G' ?_
  simpa only [G',CoherentGluing.toHomotopy,Category.assoc,nerve_constant_pre'_assoc] using hG
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalRecognition
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.boxBoundaryInclusion_mono _root_.OAI.Thomason.GeometricRecognition.simplexBoundaryInclusion_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma polyRealize_post {P : Type u} [PartialOrder P] {K L : SSet.{u}}
    (a : nerve P ⟶ K) (r : K ⟶ L) :
    polyRealize (a ≫ r) = (realizeMap r).comp (polyRealize a) := by
  rw [polyRealize,realizeMap_comp,ContinuousMap.comp_assoc]
  rfl

lemma polyRealize_order {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) : polyRealize (nerveMap i.toFunctor) =
      polyToRealizationHom.hom.comp (affineMap i) := by
  ext x
  exact polyToRealization_natural i x

lemma poly_realization_homotopy_rel {P B : Type u} [PartialOrder P] [PartialOrder B]
    (i : B →o P) (hi : Function.Injective i) {K : SSet.{u}}
    (z : nerve B ⟶ K) {a b : nerve P ⟶ K}
    (H : BasedHomotopy (nerveMap i.toFunctor) z a b) :
    Nonempty ((polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  obtain ⟨G,hG⟩ := H
  have hb := (based_homotopy_boundary _ _ ⟨G,hG⟩).2
  obtain ⟨F⟩ := realization_homotopy_rel (nerveMap i.toFunctor) G
    (by rw [hb]; exact hG)
  refine ⟨top_homotopy_rel_pre F polyToRealizationHom.hom _ ?_⟩
  rintro x ⟨y,rfl⟩
  exact ⟨polyToRealization y,polyToRealization_natural i y⟩

lemma map_constantOrder {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (q : Q) (x : PolyPoint P) :
    map (constantOrder P q) (preservesChains_monotone (constantOrder P q)) x = vertex q := by
  classical
  apply PolyPoint.ext
  ext y
  rw [map_apply]
  change (x.weights.sum fun _ value => if q = y then value else 0) = Finsupp.single q 1 y
  by_cases hy : q = y
  · subst y
    simpa only [ite_true,Finsupp.single_eq_same]
      using x.total
  · simp [hy]

lemma polyRealize_constant {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (q : Q) (x : PolyPoint P) :
    polyRealize (nerveMap (constantOrder P q).toFunctor) x = polyToRealization (vertex q) := by
  rw [polyRealize_order]
  change polyToRealization (map (constantOrder P q) (preservesChains_monotone _) x) = _
  rw [map_constantOrder]

lemma geometric_relative_order_cancel (P B : PartOrd.{u}) (i : B →o P)
    (n : ℕ) (c : CubicalPair P B i n) (Q : PartOrd.{u}) (q : Q)
    (f g : P →o Q) (hf : f.comp i = constantOrder B q) (hg : g.comp i = constantOrder B q)
    {K : SSet.{u}} (r : nerve Q ⟶ K) (hr : simplicialWeakEquivalences r)
    (H : (polyRealize (nerveMap f.toFunctor ≫ r)).HomotopyRel
      (polyRealize (nerveMap g.toFunctor ≫ r)) (Set.range (map i (preservesChains_monotone i)))) :
    ∃ G : (affineMap f).Homotopy (affineMap g),
      ∀ (t : unitInterval) (x : PolyPoint B), G (t,map i (preservesChains_monotone i) x) = vertex q := by
  have hbound (a : P →o Q) (ha : a.comp i = constantOrder B q) :
      ∀ x ∈ Set.range (map i (preservesChains_monotone i)),
        polyRealize (nerveMap a.toFunctor) x = polyToRealization (vertex q) := by
    rintro x ⟨y,rfl⟩
    have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj (nerve Q)) => F y)
      (polyRealize_pre i (nerveMap a.toFunctor))
    rw [← nerveOrderMap_comp,ha] at hh
    exact hh.symm.trans (polyRealize_constant q y)
  obtain ⟨G⟩ := cubical_relative_cancel n c.home _ c.boundary
    (realizeMap r) hr (polyToRealization (vertex q))
    (polyRealize (nerveMap f.toFunctor)) (polyRealize (nerveMap g.toFunctor))
    (hbound f hf) (hbound g hg) (by simpa only [polyRealize_post] using H)
  have he (a : P →o Q) : (realizationToPoly Q).hom.comp (polyRealize (nerveMap a.toFunctor)) =
      affineMap a := by
    rw [polyRealize_order]
    apply ContinuousMap.ext
    intro x
    exact realizationToPoly_polyToRealization (map a (preservesChains_monotone a) x)
  let G' := (G.compContinuousMap (realizationToPoly Q).hom).cast (he f) (he g)
  refine ⟨G'.toHomotopy,?_⟩
  intro t x
  have hh := G'.prop t _ ⟨x,rfl⟩
  change G' (t, map i (preservesChains_monotone i) x) = vertex q
  change G' (t, map i (preservesChains_monotone i) x) = _ at hh
  rw [hh]
  change map f (preservesChains_monotone f) (map i (preservesChains_monotone i) x) = vertex q
  have hm : map f (preservesChains_monotone f) (map i (preservesChains_monotone i) x) =
      map (f.comp i) (preservesChains_monotone (f.comp i)) x :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [hm,hf,map_constantOrder]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma poly_rel_pre_pair {P B R S : PartOrd.{u}} (i : B →o P) (j : S →o R)
    (l : R →o P) (k : S →o B) (w : l.comp j = i.comp k)
    {K : SSet.{u}} {a b : nerve P ⟶ K}
    (H : (polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) :
    Nonempty ((polyRealize (nerveMap l.toFunctor ≫ a)).HomotopyRel
      (polyRealize (nerveMap l.toFunctor ≫ b))
      (Set.range (map j (preservesChains_monotone j)))) := by
  rw [polyRealize_pre,polyRealize_pre]
  refine ⟨top_homotopy_rel_pre H (affineMap l) _ ?_⟩
  rintro x ⟨y,rfl⟩
  refine ⟨map k (preservesChains_monotone k) y,?_⟩
  change map i (preservesChains_monotone i) (map k (preservesChains_monotone k) y) = map l (preservesChains_monotone l) (map j (preservesChains_monotone j) y)
  have h₁ : map i (preservesChains_monotone i) (map k (preservesChains_monotone k) y) = map (i.comp k) (preservesChains_monotone _) y :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  have h₂ : map l (preservesChains_monotone l) (map j (preservesChains_monotone j) y) = map (l.comp j) (preservesChains_monotone _) y :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [h₁,h₂,w]

lemma pair_refinement_cancel {P B : PartOrd.{u}} (i : B →o P) (hi : Function.Injective i)
    (d : PairRefinement P B i) {K : SSet.{u}} [SSet.KanComplex K]
    (z : nerve B ⟶ K) {a b : nerve P ⟶ K}
    (ha : nerveMap i.toFunctor ≫ a = z) (hb : nerveMap i.toFunctor ≫ b = z)
    (H : BasedHomotopy (nerveMap d.j.toFunctor) (nerveMap d.k.toFunctor ≫ z)
      (nerveMap d.l.toFunctor ≫ a) (nerveMap d.l.toFunctor ≫ b)) :
    BasedHomotopy (nerveMap i.toFunctor) z a b := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
  obtain ⟨H,hH⟩ := H
  exact pair_local_injective_plain _ _ _ _
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square])
    d.local_l d.local_k z a b ha hb H (by simpa only [Category.assoc] using hH)

lemma finite_cubical_realization_faithful (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    (a b : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x)
    (hb : nerveMap i.toFunctor ≫ b = SSet.const x)
    (H : (polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a b := by
  obtain ⟨Q,q,r,e,hre,hr,he,hx⟩ := pointed_kan_ex_replacement K x
  obtain ⟨d₁,a₁,ha₁,H₁⟩ := finite_pair_order_representative Q q r e he hre P B i hi a
    (by rw [hx]; exact ha)
  have hb₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ b =
      nerveMap (constantOrder d₁.S q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,d₁.square,nerveOrderMap_comp,
      Category.assoc,hb,hx,SSet.comp_const]
  obtain ⟨d₂,b₂,hb₂,H₂⟩ := finite_pair_order_representative Q q r e he hre
    d₁.R d₁.S d₁.j d₁.injective (nerveMap d₁.l.toFunctor ≫ b) hb₁
  let a₂ : d₂.R →o Q := a₁.comp d₂.l
  have ha₂ : a₂.comp d₂.j = constantOrder d₂.S q := by
    dsimp [a₂]
    rw [OrderHom.comp_assoc,d₂.square,← OrderHom.comp_assoc,ha₁,constantOrder_comp]
  have H₁' := based_homotopy_pre (nerveMap d₁.j.toFunctor) (nerveMap d₂.j.toFunctor)
    (nerveMap d₂.l.toFunctor) (nerveMap d₂.k.toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d₂.square]) _ H₁
  simp only [nerve_constant_pre'_assoc] at H₁'
  obtain ⟨G₁⟩ := poly_realization_homotopy_rel d₂.j d₂.injective _ H₁'
  obtain ⟨G₂⟩ := poly_realization_homotopy_rel d₂.j d₂.injective _ H₂
  obtain ⟨H'⟩ := poly_rel_pre_pair i d₁.j d₁.l d₁.k d₁.square H
  obtain ⟨H''⟩ := poly_rel_pre_pair d₁.j d₂.j d₂.l d₂.k d₂.square H'
  have HH : (polyRealize (nerveMap a₂.toFunctor ≫ r)).HomotopyRel
      (polyRealize (nerveMap b₂.toFunctor ≫ r))
      (Set.range (map d₂.j (preservesChains_monotone d₂.j))) := by
    have hhh := (G₁.symm.trans H'').trans G₂
    simpa only [a₂,nerveOrderMap_comp,Category.assoc] using hhh
  obtain ⟨G,hG⟩ := geometric_relative_order_cancel d₂.R d₂.S d₂.j n
    ((c.refine d₁).refine d₂) Q q a₂ b₂ ha₂ hb₂ r hr HH
  have H₃ := pair_relative_nerve_descent d₂.R d₂.S d₂.j d₂.injective q a₂ b₂
    ha₂ hb₂ G hG K r
  have H₃' : BasedHomotopy (nerveMap d₂.j.toFunctor)
      (nerveMap (constantOrder d₂.S q).toFunctor ≫ r)
      (nerveMap d₂.l.toFunctor ≫ nerveMap a₁.toFunctor ≫ r)
      (nerveMap b₂.toFunctor ≫ r) := by
    simpa only [a₂,nerveOrderMap_comp,Category.assoc] using H₃
  let : Mono (nerveMap d₂.j.toFunctor) := nerveOrderMap_mono d₂.j d₂.injective
  have H₄ := based_homotopy_trans _ _
    (based_homotopy_trans _ _ H₁' H₃') (based_homotopy_symm _ _ H₂)
  have hax₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ a = SSet.const x := by
    rw [← Category.assoc,← nerveOrderMap_comp,d₁.square,nerveOrderMap_comp,
      Category.assoc,ha,SSet.comp_const]
  have hbx₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ b = SSet.const x := by
    rw [hb₁,hx]
  have H₅ := pair_refinement_cancel d₁.j d₁.injective d₂ (SSet.const x) hax₁ hbx₁
    (by simpa only [hx,SSet.comp_const] using H₄)
  exact pair_refinement_cancel i hi d₁ (SSet.const x) ha hb
    (by simpa only [SSet.comp_const] using H₅)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma weak_cubical_injective (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K L : SSet.{u}} [SSet.KanComplex K] (r : K ⟶ L) (hr : simplicialWeakEquivalences r)
    (x : K _⦋0⦌) (a b : nerve P ⟶ K)
    (ha : nerveMap i.toFunctor ≫ a = SSet.const x)
    (hb : nerveMap i.toFunctor ≫ b = SSet.const x)
    (H : BasedHomotopy (nerveMap i.toFunctor) (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a b := by
  obtain ⟨G⟩ := poly_realization_homotopy_rel i hi _ H
  have boundary (f : nerve P ⟶ K) (hf : nerveMap i.toFunctor ≫ f = SSet.const x) :
      ∀ y ∈ Set.range (map i (preservesChains_monotone i)), polyRealize f y =
        KanQuillen.realVertex x := by
    rintro y ⟨z,rfl⟩
    have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj K) => F z) (polyRealize_pre i f)
    rw [hf] at hh
    exact hh.symm.trans (polyRealize_const x z)
  obtain ⟨G'⟩ := cubical_relative_cancel n c.home _ c.boundary (realizeMap r) hr
    (KanQuillen.realVertex x) (polyRealize a) (polyRealize b) (boundary a ha) (boundary b hb)
    (by simpa only [polyRealize_post] using G)
  exact finite_cubical_realization_faithful P B i hi n c x a b ha hb G'
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma pointed_replacement_real_vertex {Q : Type u} [PartialOrder Q] (q : Q)
    {K : SSet.{u}} (r : nerve Q ⟶ K) (x : K _⦋0⦌)
    (hx : nerveMap (constantOrder Q q).toFunctor ≫ r = SSet.const x) :
    realizeMap r (polyToRealization (vertex q)) = KanQuillen.realVertex x := by
  have hh := congrArg (fun F : C(PolyPoint Q,SSet.toTop.obj K) => F (vertex q))
    (polyRealize_post (nerveMap (constantOrder Q q).toFunctor) r)
  rw [hx] at hh
  change polyRealize (SSet.const x) (vertex q) =
    realizeMap r (polyRealize (nerveMap (constantOrder Q q).toFunctor) (vertex q)) at hh
  rw [polyRealize_const,polyRealize_constant] at hh
  exact hh.symm

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma finite_cubical_geometric_representative (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) (c : CubicalPair P (PartOrd.of B) (inclusion B) n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    (f : C(PolyPoint P,SSet.toTop.obj K))
    (hf : ∀ y ∈ Set.range (map (inclusion B) (preservesChains_monotone _)),
      f y = KanQuillen.realVertex x) :
    ∃ b : nerve P ⟶ K, nerveMap (inclusion B).toFunctor ≫ b = SSet.const x ∧
      Nonempty ((polyRealize b).HomotopyRel f
        (Set.range (map (inclusion B) (preservesChains_monotone _)))) := by
  obtain ⟨Q,q,r,hr,hw,hx⟩ := pointed_kan_poset_replacement K x
  have hv := pointed_replacement_real_vertex q r x (hx Q)
  obtain ⟨g,hg,⟨G⟩⟩ := cubical_relative_surject n c.home _ c.boundary (realizeMap r) hw
    (polyToRealization (vertex q)) f (by simpa only [hv] using hf)
  let g' : C(PolyPoint P,PolyPoint Q) := (realizationToPoly Q).hom.comp g
  have hg' (y : PolyPoint B) : g' (map (inclusion B) (preservesChains_monotone _) y) = vertex q := by
    change realizationToPoly Q (g _) = _
    rw [hg _ ⟨y,rfl⟩,realizationToPoly_polyToRealization]
  obtain ⟨m,a,H,ha,hH⟩ := pair_geometric_approximation P B q g' hg'
  have hab : nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m).toFunctor ≫
      nerveMap a.toFunctor ≫ r =
        nerveMap (last (PartOrd.of B) m).toFunctor ≫ SSet.const x := by
    rw [← Category.assoc,← nerveOrderMap_comp,ha]
    exact (hx _).trans (SSet.comp_const _ _).symm
  obtain ⟨b,D,hb,hD⟩ := descend_pair_approximation P B m K (SSet.const x)
    (nerveMap a.toFunctor ≫ r) hab
  have hD' : BasedHomotopy (nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m).toFunctor)
      (SSet.const x) (nerveMap (last P m).toFunctor ≫ b) (nerveMap a.toFunctor ≫ r) :=
    ⟨D,by simpa only [SSet.comp_const] using hD⟩
  obtain ⟨D'⟩ := poly_realization_homotopy_rel
    (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
    (levelMap_injective _ Subtype.val_injective m) _ hD'
  obtain ⟨L⟩ := last_barycentric_realization_rel P B m x b hb
  let H' : (polyRealize (nerveMap a.toFunctor ≫ r)).HomotopyRel
      (((realizeMap r).comp g).comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩)
      (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
        (preservesChains_monotone _))) := by
    have he : ((realizeMap r).comp polyToRealizationHom.hom).comp
        (g'.comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩) =
        ((realizeMap r).comp g).comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩ := by
      ext y
      change realizeMap r (polyToRealization (realizationToPoly Q (g _))) = _
      rw [polyToRealization_realizationToPoly]
      rfl
    refine { toHomotopy := ((ContinuousMap.Homotopy.refl
      ((realizeMap r).comp polyToRealizationHom.hom)).comp H).cast ?_ he
             prop' := ?_ }
    · rw [polyRealize_post,polyRealize_order,ContinuousMap.comp_assoc]
    · rintro t y ⟨z,rfl⟩
      change realizeMap r (polyToRealization (H (t,_))) = polyRealize (nerveMap a.toFunctor ≫ r) _
      rw [hH]
      have hh := poly_realize_boundary
        (P := level P m) (B := level (PartOrd.of B) m)
        (levelMap (inclusion B) m) x (nerveMap a.toFunctor ≫ r)
        (by simpa only [SSet.comp_const] using hab)
      exact hv.trans (hh _ ⟨z,rfl⟩).symm
  let G' := top_homotopy_rel_pre G
    ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩
    (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
      (preservesChains_monotone _))) (by
      rintro y ⟨z,rfl⟩
      exact ⟨levelHomeomorph (PartOrd.of B) m z, (levelHomeomorph_natural _ Subtype.val_injective m z).symm⟩)
  let F := ((L.symm.trans D').trans H').trans G'
  have F' := top_homotopy_rel_pre F
    ⟨(levelHomeomorph P m).symm,(levelHomeomorph P m).symm.continuous⟩ _
    (full_pair_home_boundary P B m)
  refine ⟨b,hb,⟨F'.cast ?_ ?_⟩⟩ <;> ext y <;>
    simp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma weak_cubical_surjective (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) (c : CubicalPair P (PartOrd.of B) (inclusion B) n)
    {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a : nerve P ⟶ L) (ha : nerveMap (inclusion B).toFunctor ≫ a = SSet.const (r.app _ x)) :
    ∃ b : nerve P ⟶ K, nerveMap (inclusion B).toFunctor ≫ b = SSet.const x ∧
      BasedHomotopy (nerveMap (inclusion B).toFunctor) (SSet.const (r.app _ x)) (b ≫ r) a := by
  have hf := poly_realize_boundary (P := P) (B := PartOrd.of B) (inclusion B) (r.app _ x) a ha
  obtain ⟨g,hg,⟨G⟩⟩ := cubical_relative_surject n c.home _ c.boundary (realizeMap r) hr
    (KanQuillen.realVertex x) (polyRealize a) (by simpa only [realVertex_natural] using hf)
  obtain ⟨b,hb,⟨H⟩⟩ := finite_cubical_geometric_representative P B n c x g hg
  refine ⟨b,hb,finite_cubical_realization_faithful P (PartOrd.of B) (inclusion B)
    Subtype.val_injective n c (r.app _ x) (b ≫ r) a ?_ ha ?_⟩
  · rw [← Category.assoc,hb,SSet.const_comp]
  · have F := (H.compContinuousMap (realizeMap r)).trans G
    exact F.cast (polyRealize_post b r).symm rfl
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def realizeCubeMap (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) (a : CubeMap n x) :
    GenLoop (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
  ⟨(polyRealize a.val).comp ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩,by
    intro y hy
    exact poly_realize_boundary (P := cubePoset n) (B := PartOrd.of (cubeBoundary n))
      (cubeBoundaryInclusion n) x a.val a.property _
      ((actualCubicalPair n).boundary _ |>.mpr (by simpa using hy))⟩

lemma realizeCubeMap_homotopic (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌)
    {a b : CubeMap n x}
    (H : BasedHomotopy (nerveMap (cubeBoundaryInclusion n).toFunctor) (SSet.const x) a.val b.val) :
    GenLoop.Homotopic (realizeCubeMap n x a) (realizeCubeMap n x b) := by
  obtain ⟨G⟩ := poly_realization_homotopy_rel (cubeBoundaryInclusion n) Subtype.val_injective _ H
  exact ⟨top_homotopy_rel_pre G
    ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩
    (Cube.boundary (Fin (n+1))) (fun y hy =>
      ((actualCubicalPair n).boundary _).mpr (by simpa using hy))⟩

def realizeCubeClasses (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :
    CubeClasses n x → HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
  Quotient.map (realizeCubeMap n x) (fun _ _ h => realizeCubeMap_homotopic n x h)

theorem positive_realization_comparison (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K]
    (x : K _⦋0⦌) : Function.Bijective (realizeCubeClasses n x) := by
  constructor
  · intro a b hab
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective b
    obtain ⟨H⟩ : GenLoop.Homotopic (realizeCubeMap n x a) (realizeCubeMap n x b) := Quotient.exact hab
    have G := top_homotopy_rel_pre H
      ⟨(actualCubicalPair n).home,(actualCubicalPair n).home.continuous⟩
      (Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _)))
      (fun y hy => ((actualCubicalPair n).boundary y).mp hy)
    have G' : (polyRealize a.val).HomotopyRel (polyRealize b.val)
        (Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _))) :=
      G.cast (by ext y; simp [realizeCubeMap]) (by ext y; simp [realizeCubeMap])
    exact Quotient.sound (finite_cubical_realization_faithful _ _ _ Subtype.val_injective
      n (actualCubicalPair n) x a.val b.val a.property b.property G')
  · intro a
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    let f := a.val.comp ⟨(actualCubicalPair n).home,(actualCubicalPair n).home.continuous⟩
    have hf : ∀ y ∈ Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _)),
        f y = KanQuillen.realVertex x := fun y hy => a.property _ (((actualCubicalPair n).boundary y).mp hy)
    obtain ⟨b,hb,⟨H⟩⟩ := finite_cubical_geometric_representative (cubePoset n) (cubeBoundary n)
      n (actualCubicalPair n) x f hf
    refine ⟨⟦⟨b,hb⟩⟧,Quotient.sound ⟨?_⟩⟩
    have G := top_homotopy_rel_pre H
      ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩
      (Cube.boundary (Fin (n+1))) (fun y hy =>
        ((actualCubicalPair n).boundary _).mpr (by simpa using hy))
    exact G.cast rfl (by ext y; simp [f])
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Boxes. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma simplex_subdivide_boundary (m : ℕ) (x : PolyPoint (simplexPoset.{u} m)) :
    (∃ y : PolyPoint (simplexBoundary m), map (inclusion (simplexBoundary m))
      (preservesChains_monotone _) y = x) ↔
      ∃ i, (simplexPolyCoordinates m (subdivide x)).weights i = 0 := by
  classical
  rw [exists_of_support]
  have hne : x.weights.support.Nonempty := (supportIndex x).nonempty
  obtain ⟨s,hs,hm⟩ := flag_has_max _ x.chain hne
  have hsupport : (subdivide x).weights.support = s.finset := by
    change (barycentricLinear x.weights).support = _
    rw [barycentricLinear_support_eq _ x.nonneg,flag_union_eq_max _ s hs hm]
  constructor
  · intro h
    have hh : s.finset ≠ Finset.univ := h s hs
    have hex : ∃ i, i ∉ s.finset := by
      by_contra! h
      exact hh (Finset.eq_univ_of_forall h)
    obtain ⟨i,hi⟩ := hex
    refine ⟨i.down,?_⟩
    change (subdivide x).weights i = 0
    exact Finsupp.notMem_support_iff.mp (by simpa only [hsupport] using hi)
  · rintro ⟨i,hi⟩ t ht he
    have hi' : ULift.up i ∉ (subdivide x).weights.support := Finsupp.notMem_support_iff.mpr hi
    rw [hsupport] at hi'
    exact hi' (hm t ht (he ▸ Finset.mem_univ _))

def simplexCubicalPair (n : ℕ) : CubicalPair (simplexPoset.{u} (n+1))
    (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1))) n where
  home := subdivisionHomeomorph.trans ((simplexPolyHomeomorph (n+1)).trans
    (SimplexGeometry.simplexCubeHomeomorph (n+1)))
  boundary x := (simplex_subdivide_boundary (n+1) x).trans
    (SimplexGeometry.simplexCubeHomeomorph_boundary (n+1) _)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

theorem weak_simplex_injective (n : ℕ) {K L : SSet.{u}} [SSet.KanComplex K]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a b : (Δ[n+1] : SSet.{u}) ⟶ K)
    (ha : (SSet.boundary (n+1)).ι ≫ a = SSet.const x)
    (hb : (SSet.boundary (n+1)).ι ≫ b = SSet.const x)
    (H : BasedHomotopy (SSet.boundary (n+1)).ι (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (SSet.boundary (n+1)).ι (SSet.const x) a b := by
  let f := simplexPairProjection.{u} (n+1)
  let g := simplexBoundaryProjection.{u} (n+1)
  let j := nerveMap (inclusion (simplexBoundary.{u} (n+1))).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const x := by
    rw [← Category.assoc,simplex_pair_square,Category.assoc,ha,SSet.comp_const]
  have hb' : j ≫ f ≫ b = SSet.const x := by
    rw [← Category.assoc,simplex_pair_square,Category.assoc,hb,SSet.comp_const]
  have H' : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ a) ≫ r) ((f ≫ b) ≫ r) := by
    simpa only [SSet.comp_const,Category.assoc] using based_homotopy_pre
      _ j f g (simplex_pair_square _) _ H
  obtain ⟨G,hG⟩ := weak_cubical_injective (simplexPoset (n+1))
    (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1)))
    Subtype.val_injective n (simplexCubicalPair n) r hr x (f ≫ a) (f ≫ b) ha' hb' H'
  exact pair_local_injective_plain _ j f g (simplex_pair_square _)
    (simplexPairProjection_local _) (simplexBoundaryProjection_local _) _ a b ha hb G
    (by simpa only [SSet.comp_const] using hG)

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

theorem weak_box_injective (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a b : nerve (Finset I) ⟶ K)
    (ha : (boxBoundary I).ι ≫ a = SSet.const x)
    (hb : (boxBoundary I).ι ≫ b = SSet.const x)
    (H : BasedHomotopy (boxBoundary I).ι (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (boxBoundary I).ι (SSet.const x) a b := by
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const x := by
    rw [← Category.assoc,box_pair_square,Category.assoc,ha,SSet.comp_const]
  have hb' : j ≫ f ≫ b = SSet.const x := by
    rw [← Category.assoc,box_pair_square,Category.assoc,hb,SSet.comp_const]
  have H' : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ a) ≫ r) ((f ≫ b) ≫ r) := by
    simpa only [SSet.comp_const,Category.assoc] using based_homotopy_pre
      _ j f g (box_pair_square _) _ H
  obtain ⟨G,hG⟩ := weak_cubical_injective (PartOrd.of (NonemptyFiniteChains (Finset I)))
    (PartOrd.of (Cubical.boundaryFaces I)) (inclusion (Cubical.boundaryFaces I))
    Subtype.val_injective n (finiteBoxPair I n e) r hr x (f ≫ a) (f ≫ b) ha' hb' H'
  exact pair_local_injective_plain _ j f g (box_pair_square _)
    (boxPairProjection_local _) (boxBoundaryProjection_local _) _ a b ha hb G
    (by simpa only [SSet.comp_const] using hG)

theorem weak_box_surjective (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a : nerve (Finset I) ⟶ L)
    (ha : (boxBoundary I).ι ≫ a = SSet.const (r.app _ x)) :
    ∃ b : nerve (Finset I) ⟶ K, (boxBoundary I).ι ≫ b = SSet.const x ∧
      BasedHomotopy (boxBoundary I).ι (SSet.const (r.app _ x)) (b ≫ r) a := by
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const (r.app _ x) := by
    rw [← Category.assoc,box_pair_square,Category.assoc,ha,SSet.comp_const]
  obtain ⟨b',hb',H'⟩ := weak_cubical_surjective (PartOrd.of (NonemptyFiniteChains (Finset I)))
    (Cubical.boundaryFaces I) n (finiteBoxPair I n e) r hr x (f ≫ a) ha'
  obtain ⟨b,G,hb,hG⟩ := pair_local_surjective_plain (boxBoundary I).ι j f g
    (box_pair_square _) (boxPairProjection_local _) (boxBoundaryProjection_local _)
    (SSet.const x) b' (by simpa only [SSet.comp_const] using hb')
  have HG : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ b) ≫ r) (b' ≫ r) := by
    simpa only [SSet.comp_const,SSet.const_comp] using
      based_homotopy_post j (SSet.const x) ⟨G,by simpa only [SSet.comp_const] using hG⟩ r
  obtain ⟨F,hF⟩ := based_homotopy_trans j (SSet.const (r.app _ x)) HG H'
  let F' : SSet.Homotopy (f ≫ (b ≫ r)) (f ≫ a) := CoherentGluing.toHomotopy F.h
    (by simpa only [Category.assoc] using F.h₀) F.h₁
  refine ⟨b,hb,pair_local_injective_plain _ j f g (box_pair_square _)
    (boxPairProjection_local _) (boxBoundaryProjection_local _)
    (SSet.const (r.app _ x)) (b ≫ r) a ?_ ha F' ?_⟩
  · rw [← Category.assoc,hb,SSet.const_comp]
  · simpa only [F', CoherentGluing.toHomotopy, SSet.comp_const] using hF
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

lemma simplex_homotopic_const {K : SSet.{u}} (n : ℕ) (a : Δ[n] ⟶ K) :
    ∃ x : K _⦋0⦌, Homotopic a (SSet.const x) := by
  let P := ULift.{u} (Fin (n+1))
  let q : P := ⟨0⟩
  let v : (nerve P) _⦋0⦌ := (Functor.const (Fin 1)).obj q
  let e := SSet.stdSimplex.isoNerve.{u} n
  have H : Homotopic (nerveMap (constantOrder P q).toFunctor) (𝟙 (nerve P)) :=
    homotopic_of_homotopy (orderHomotopy (constantOrder P q) OrderHom.id (fun x => Fin.zero_le x.down))
  have hc : nerveMap (constantOrder P q).toFunctor = SSet.const v := nerve_constant_vertex v
  rw [hc] at H
  have H' := homotopic_pre e.hom (homotopic_post H (e.inv ≫ a))
  refine ⟨(e.inv ≫ a).app _ v, homotopic_symm ?_⟩
  simpa only [SSet.const_comp,SSet.comp_const,Category.id_comp,← Category.assoc,
    Iso.hom_inv_id,Category.id_comp, NatTrans.comp_app, types_comp_apply] using H'

lemma straighten_boundary {K : SSet.{u}} [SSet.KanComplex K]
    (n : ℕ) (a : (∂Δ[n+1] : SSet.{u}) ⟶ K) :
    ∃ x : K _⦋0⦌, ∃ b : (∂Δ[n+1] : SSet.{u}) ⟶ K,
      Homotopic a b ∧ hornInBoundary n ≫ b = SSet.const x := by
  obtain ⟨g,hg⟩ := SSet.KanComplex.hornFilling (hornInBoundary n ≫ a)
  obtain ⟨x,H⟩ := simplex_homotopic_const (n+1) g
  have H' := homotopic_pre (SSet.horn (n+1) 0).ι H
  rw [← hg,SSet.comp_const] at H'
  obtain ⟨G⟩ := homotopy_of_homotopic H'
  obtain ⟨b,Gb,hb,_⟩ := homotopy_extension (hornInBoundary n) a G
  exact ⟨x,b,homotopic_of_homotopy Gb,hb⟩

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

theorem terminal_rlp_of_nullsimplices {K : SSet.{u}} [SSet.KanComplex K]
    (x₀ : K _⦋0⦌)
    (h : ∀ (n : ℕ) (x : K _⦋0⦌) (a : Δ[n] ⟶ K),
      (SSet.boundary n).ι ≫ a = SSet.const x →
      BasedHomotopy (SSet.boundary n).ι (SSet.const x) a (SSet.const x)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro a b sq
  cases n with
  | zero =>
    exact ⟨⟨{ l := SSet.const x₀, fac_left := SSet.boundary.hom_ext₀, fac_right := Subsingleton.elim _ _ }⟩⟩
  | succ n =>
    obtain ⟨x,c,Hac,hc⟩ := straighten_boundary n a
    have he : (SSet.boundary n).ι ≫ (SSet.boundary.ι (0 : Fin (n+2)) ≫ c) =
        SSet.const x := by
      rw [← Category.assoc,boundaryInHorn_square,Category.assoc,hc,SSet.comp_const]
    obtain ⟨H⟩ := nullhomotopy_boundary_of_face n x c hc (h n x _ he)
    have H' := homotopic_symm (homotopic_trans Hac (homotopic_of_homotopy H))
    obtain ⟨G⟩ := homotopy_of_homotopic H'
    have G' : SSet.Homotopy ((SSet.boundary (n+1)).ι ≫ SSet.const x) a := by
      simpa only [SSet.comp_const] using G
    obtain ⟨l,_,hl,_⟩ := homotopy_extension (SSet.boundary (n+1)).ι (SSet.const x) G'
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := Subsingleton.elim _ _ }⟩⟩

theorem weak_terminal_rlp {K : SSet.{u}} [SSet.KanComplex K]
    (hw : simplicialWeakEquivalences (terminal.from K)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  let p := terminal.from K
  let v : (⊤_ SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (terminal.from (Δ[0] : SSet.{u}))
  obtain ⟨z,hz⟩ := (KanQuillen.map_components_bijective_of_weak p hw).2 (SSet.π₀.mk v)
  obtain ⟨z,rfl⟩ := SSet.π₀.mk_surjective z
  apply terminal_rlp_of_nullsimplices z
  intro n x a ha
  cases n with
  | zero =>
    have hv : SSet.π₀.mk (SSet.yonedaEquiv a) = SSet.π₀.mk x := by
      apply (KanQuillen.map_components_bijective_of_weak p hw).1
      apply congrArg SSet.π₀.mk
      apply SSet.yonedaEquiv.symm.injective
      subsingleton
    obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const hv)
    have H' : SSet.Homotopy a (SSet.const x) := by
      simpa only [← SSet.yonedaEquiv_symm_zero,Equiv.symm_apply_apply] using H
    exact based_homotopy_zero x H'
  | succ n =>
    apply weak_simplex_injective n p hw x a (SSet.const x) ha (SSet.comp_const _ _)
    have he : a ≫ p = SSet.const x ≫ p := Subsingleton.elim _ _
    rw [he]
    exact based_homotopy_refl _ _ _ (by rw [← Category.assoc,SSet.comp_const,SSet.const_comp])
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma correct_box_nullhomotopy (I : Type u) [Fintype I] [LinearOrder I]
    {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x : K _⦋0⦌) {a : nerve (Finset I) ⟶ K}
    (ha : a ≫ p = SSet.const (p.app _ x))
    (H : SSet.Homotopy a (SSet.const x))
    (hH : (boxBoundary I).ι ▷ Δ[1] ≫ H.h = SSet.const x) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      (boxBoundary I).ι ▷ Δ[1] ≫ F.h = SSet.const x ∧
      F.h ≫ p = SSet.const (p.app _ x) := by
  let : LinearOrder (Option I) := LinearOrder.lift' (Fintype.equivFin (Option I))
    (Fintype.equivFin (Option I)).injective
  have hb : (boxBoundary (Option I)).ι ≫ boxToPrism I ≫ H.h ≫ p = SSet.const (p.app _ x) :=
    boxPrism_boundary_const I (p.app _ x) (H.h ≫ p)
      (by rw [← Category.assoc,hH,SSet.const_comp])
      (by rw [← Category.assoc,H.h₀,ha])
      (by rw [← Category.assoc,H.h₁,SSet.const_comp])
  obtain ⟨b,hb,Gb⟩ := weak_box_surjective (Option I) (Fintype.card I)
    (Fintype.equivFinOfCardEq (by simp)) p hw x (boxToPrism I ≫ H.h ≫ p) hb
  have hm : (prismToBox I ≫ b) ≫ p = prismToBox I ≫ (b ≫ p) := Category.assoc _ _ _
  have hj₀ : SSet.ι₀ ≫ prismToBox I ≫ b = SSet.const x := by
    rw [← Category.assoc,← prismBoxEnd_zero_comp,Category.assoc,hb,SSet.comp_const]
  have hj₁ : SSet.ι₁ ≫ prismToBox I ≫ b = SSet.const x := by
    rw [← Category.assoc,← prismBoxEnd_one_comp,Category.assoc,hb,SSet.comp_const]
  let J : SSet.Homotopy (SSet.const (X := nerve (Finset I)) x) (SSet.const x) :=
    CoherentGluing.toHomotopy (prismToBox I ≫ b) hj₀ hj₁
  have hj : (boxBoundary I).ι ▷ Δ[1] ≫ J.h = SSet.const x := by
    change (boxBoundary I).ι ▷ Δ[1] ≫ prismToBox I ≫ b = _
    rw [← Category.assoc,← prismBoxSide_comp,Category.assoc,hb,SSet.comp_const]
  obtain ⟨G,hG⟩ := based_homotopy_symm (boxBoundary (Option I)).ι (SSet.const (p.app _ x)) Gb
  let G' : SSet.Homotopy (H.h ≫ p) (J.h ≫ p) := CoherentGluing.toHomotopy
    (prismToBox I ▷ Δ[1] ≫ G.h)
    (by rw [SSet.ι₀_comp_assoc,G.h₀,← Category.assoc];
        change ((boxPrismIso I).inv ≫ (boxPrismIso I).hom) ≫ _ = _;
        rw [Iso.inv_hom_id,Category.id_comp])
    (by rw [SSet.ι₁_comp_assoc,G.h₁]; rfl)
  have hg : (boxBoundary (Option I)).ι ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x) := by
    simpa only [SSet.comp_const] using hG
  apply correct_nullhomotopy_to_fiber (boxBoundary I).ι p hp x H J hH hj G'
  · change (boxBoundary I).ι ▷ Δ[1] ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxSide_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]
  · change SSet.ι₀ ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxEnd_zero_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]
  · change SSet.ι₁ ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxEnd_one_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]

lemma weak_fibration_box_nullhomotopy (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x : K _⦋0⦌) (a : nerve (Finset I) ⟶ K)
    (hab : (boxBoundary I).ι ≫ a = SSet.const x)
    (ha : a ≫ p = SSet.const (p.app _ x)) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      (boxBoundary I).ι ▷ Δ[1] ≫ F.h = SSet.const x ∧
      F.h ≫ p = SSet.const (p.app _ x) := by
  have H : BasedHomotopy (boxBoundary I).ι (SSet.const (p.app _ x))
      (a ≫ p) (SSet.const x ≫ p) := by
    rw [ha,SSet.const_comp]
    exact based_homotopy_refl _ _ _ (SSet.comp_const _ _)
  obtain ⟨H,hH⟩ := weak_box_injective I n e p hw x a (SSet.const x) hab (SSet.comp_const _ _) H
  exact correct_box_nullhomotopy I p hp hw x ha H (by simpa only [SSet.comp_const] using hH)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity PolyPoint

lemma weak_fibration_vertex_homotopy {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x z : K _⦋0⦌) (hz : p.app _ z = p.app _ x) :
    ∃ F : SSet.Homotopy (SSet.const (X := Δ[0]) z) (SSet.const x),
      F.h ≫ p = SSet.const (p.app _ x) := by
  have hc : SSet.π₀.mk z = SSet.π₀.mk x := by
    apply (KanQuillen.map_components_bijective_of_weak p hw).1
    exact congrArg SSet.π₀.mk hz
  obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const hc)
  let I := ULift.{u} (Fin 0)
  let A := nerve (Finset I)
  let q : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
  let H' : SSet.Homotopy (SSet.const (X := A) z) (SSet.const x) :=
    homotopy_pre q H
  have hH : (boxBoundary I).ι ▷ Δ[1] ≫ H'.h = SSet.const x := by
    ext n st
    obtain ⟨i,hi⟩ := st.1.property
    exact Fin.elim0 i.down
  obtain ⟨F,hF,hFp⟩ := correct_box_nullhomotopy I p hp hw x
    (by rw [SSet.const_comp,hz]) H' hH
  let v : A _⦋0⦌ := (⟨fun _ : Fin 1 => (∅ : Finset I), fun _ _ _ => le_rfl⟩ : Fin 1 →o Finset I).toFunctor
  let j : (Δ[0] : SSet.{u}) ⟶ A := SSet.const v
  refine ⟨homotopy_pre j F,?_⟩
  change (j ▷ Δ[1] ≫ F.h) ≫ p = _
  rw [Category.assoc,hFp,SSet.comp_const]

lemma strictFiber_vertex_homotopy {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) (x z : (strictFiber p y : SSet) _⦋0⦌) :
    Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) z) (SSet.const x)) := by
  have hx : p.app _ x.val = y := (strictFiber_vertex_iff p y x.val).mp x.property
  have hz : p.app _ z.val = y := (strictFiber_vertex_iff p y z.val).mp z.property
  obtain ⟨H,hH⟩ := weak_fibration_vertex_homotopy p hp hw x.val z.val (hz.trans hx.symm)
  let H' : SSet.Homotopy (SSet.const (X := Δ[0]) z ≫ (strictFiber p y).ι)
      (SSet.const x ≫ (strictFiber p y).ι) :=
    CoherentGluing.toHomotopy H.h (by rw [SSet.const_comp]; exact H.h₀)
      (by rw [SSet.const_comp]; exact H.h₁)
  exact strictFiber_homotopy p y H' (by simpa only [H',CoherentGluing.toHomotopy,hx] using hH)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma cubical_null_of_group_subsingleton (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    [Subsingleton (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x))]
    (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a (SSet.const x) := by
  let loop (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
      GenLoop (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
    ⟨(polyRealize a).comp ⟨c.home.symm,c.home.symm.continuous⟩,by
      intro y hy
      exact poly_realize_boundary i x a ha _ ((c.boundary _).mpr (by simpa using hy))⟩
  have he : (⟦loop a ha⟧ : HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x)) =
      ⟦loop (SSet.const x) (SSet.comp_const _ _)⟧ :=
    @Subsingleton.elim (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x))
      inferInstance _ _
  obtain ⟨G⟩ : GenLoop.Homotopic (loop a ha) (loop (SSet.const x) (SSet.comp_const _ _)) :=
    Quotient.exact he
  have H := top_homotopy_rel_pre G ⟨c.home,c.home.continuous⟩ _
    (fun y hy => (c.boundary y).mp hy)
  have H' : (polyRealize a).HomotopyRel (polyRealize (SSet.const x))
      (Set.range (map i (preservesChains_monotone i))) :=
    H.cast (by ext y; simp [loop]) (by ext y; simp [loop])
  exact finite_cubical_realization_faithful P B i hi n c x a (SSet.const x)
    ha (SSet.comp_const _ _) H'

lemma cube_classes_subsingleton_of_boxes {K : SSet.{u}} [SSet.KanComplex K]
    (n : ℕ) (x : K _⦋0⦌)
    (h : ∀ a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ K,
      (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x →
      BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x)) :
    Subsingleton (CubeClasses n x) := by
  let I := ULift.{u} (Fin (n+1))
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (cubeBoundaryInclusion.{u} n).toFunctor
  have hc (a : CubeMap n x) : BasedHomotopy j (SSet.const x) a.val (SSet.const x) := by
    obtain ⟨b,G,hb,hG⟩ := pair_local_surjective_plain (boxBoundary I).ι j f g
      (box_pair_square I) (boxPairProjection_local I) (boxBoundaryProjection_local I)
      (SSet.const x) a.val (by simpa only [SSet.comp_const] using a.property)
    have H := based_homotopy_pre (boxBoundary I).ι j f g (box_pair_square I) (SSet.const x) (h b hb)
    have H' : BasedHomotopy j (SSet.const x) (f ≫ b) (SSet.const x) := by
      simpa only [SSet.comp_const] using H
    exact based_homotopy_trans j (SSet.const x)
      (based_homotopy_symm j (SSet.const x) ⟨G,by simpa only [SSet.comp_const] using hG⟩) H'
  constructor
  intro a b
  obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective b
  exact Quotient.sound (based_homotopy_trans j (SSet.const x) (hc a)
    (based_homotopy_symm j (SSet.const x) (hc b)))

theorem terminal_rlp_of_nullboxes {K : SSet.{u}} [SSet.KanComplex K]
    (x₀ : K _⦋0⦌)
    (h₀ : ∀ x y : K _⦋0⦌, Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) x) (SSet.const y)))
    (h : ∀ (n : ℕ) (x : K _⦋0⦌) (a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ K),
      (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x →
      BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  apply terminal_rlp_of_nullsimplices x₀
  intro n x a ha
  cases n with
  | zero =>
    obtain ⟨H⟩ := h₀ (SSet.yonedaEquiv a) x
    have H' : SSet.Homotopy a (SSet.const x) := by
      simpa only [← SSet.yonedaEquiv_symm_zero,Equiv.symm_apply_apply] using H
    exact based_homotopy_zero x H'
  | succ n =>
    let := cube_classes_subsingleton_of_boxes n x (h n x)
    let : Subsingleton (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x)) :=
      Function.Surjective.subsingleton (positive_realization_comparison n x).2
    let f := simplexPairProjection.{u} (n+1)
    let g := simplexBoundaryProjection.{u} (n+1)
    let j := nerveMap (inclusion (simplexBoundary.{u} (n+1))).toFunctor
    have ha' : j ≫ f ≫ a = SSet.const x := by
      rw [← Category.assoc,simplex_pair_square,Category.assoc,ha,SSet.comp_const]
    obtain ⟨G,hG⟩ := cubical_null_of_group_subsingleton (simplexPoset (n+1))
      (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1)))
      Subtype.val_injective n (simplexCubicalPair n) x (f ≫ a) ha'
    let G' : SSet.Homotopy (f ≫ a) (f ≫ SSet.const x) :=
      CoherentGluing.toHomotopy G.h G.h₀ (by simpa only [SSet.comp_const] using G.h₁)
    exact pair_local_injective_plain _ j f g (simplex_pair_square _)
      (simplexPairProjection_local _) (simplexBoundaryProjection_local _) _ a (SSet.const x)
      ha (SSet.comp_const _ _) G' (by simpa only [G',CoherentGluing.toHomotopy,SSet.comp_const] using hG)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma strictFiber_based_box_null {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) (n : ℕ) (x : (strictFiber p y : SSet) _⦋0⦌)
    (a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ (strictFiber p y : SSet))
    (ha : (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x) :
    BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x) := by
  have hx : p.app _ x.val = y := (strictFiber_vertex_iff p y x.val).mp x.property
  obtain ⟨H,hH,hHp⟩ := weak_fibration_box_nullhomotopy (ULift.{u} (Fin (n+1)))
    n Equiv.ulift p hp hw x.val (a ≫ (strictFiber p y).ι)
    (by rw [← Category.assoc,ha,SSet.const_comp]; rfl)
    (by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const,hx])
  let H' : SSet.Homotopy a (SSet.const x) := CoherentGluing.toHomotopy
    (strictFiberLift p y H.h (by simpa only [hx] using hHp))
    (by apply (cancel_mono (strictFiber p y).ι).mp
        rw [Category.assoc,strictFiberLift_ι,H.h₀])
    (by apply (cancel_mono (strictFiber p y).ι).mp
        rw [Category.assoc,strictFiberLift_ι,H.h₁,SSet.const_comp]; rfl)
  refine ⟨H',?_⟩
  apply (cancel_mono (strictFiber p y).ι).mp
  change (_ ≫ strictFiberLift p y H.h (by simpa only [hx] using hHp)) ≫ (strictFiber p y).ι = _
  rw [Category.assoc,strictFiberLift_ι,hH,SSet.comp_const,SSet.const_comp]
  rfl

theorem weak_kan_fibration_fiber_rlp {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) : SSet.modelCategoryQuillen.I.rlp (terminal.from (strictFiber p y : SSet)) := by
  let := strictFiber_kan p hp y
  obtain ⟨x,hx⟩ := KanQuillen.weak_fibration_surjective_vertices p hp hw y
  have hx' : x ∈ (strictFiber p y).obj (op ⦋0⦌) := (strictFiber_vertex_iff p y x).mpr hx
  apply terminal_rlp_of_nullboxes (K := (strictFiber p y : SSet)) ⟨x,hx'⟩
  · intro a b
    exact strictFiber_vertex_homotopy p hp hw y b a
  · intro n a b hb
    exact strictFiber_based_box_null p hp hw y n a b hb
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanQuillen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Quillen. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition
open Subdivision

lemma weak_kan_fibration_rlp {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    SSet.modelCategoryQuillen.I.rlp p :=
  fibration_rlp_of_fibers p hp (weak_kan_fibration_fiber_rlp p hp hw)

theorem weak_fibration_rlp {K L : SSet.{u}} (p : K ⟶ L)
    (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    SSet.modelCategoryQuillen.I.rlp p := by
  let : SSet.KanComplex (exInfinityFunctor.obj K) := exInfinity_kan K
  let : SSet.KanComplex (exInfinityFunctor.obj L) := exInfinity_kan L
  have he : SSet.modelCategoryQuillen.I.rlp (exInfinityFunctor.map p) :=
    weak_kan_fibration_rlp _ (exInfinity_fibration p hp) ((exInfinity_map_weak_iff p).mpr hw)
  apply fibration_rlp_of_fibers p hp
  intro y
  let := strictFiber_kan p hp y
  apply weak_terminal_rlp
  apply (exInfinity_map_weak_iff (terminal.from (strictFiber p y : SSet))).mp
  apply KanQuillen.boundary_right_weak
  exact SSet.modelCategoryQuillen.I.rlp.of_isPullback
    ((strictFiber_isPullback p y).map exInfinityFunctor) he

theorem boundary_right_class : SSet.modelCategoryQuillen.I.rlp.{u} =
    simplicialFibrations ⊓ simplicialWeakEquivalences := by
  apply le_antisymm
  · intro K L p hp
    exact ⟨KanQuillen.boundary_right_fibrations p hp,KanQuillen.boundary_right_weak p hp⟩
  · intro K L p hp
    exact weak_fibration_rlp p hp.1 hp.2
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason.KanQuillen
open SSet.modelCategoryQuillen

lemma anodyne_class : SSet.anodyneExtensions.{u} =
    monomorphisms SSet ⊓ simplicialWeakEquivalences := by
  apply le_antisymm (le_inf anodyne_monomorphism anodyne_weak)
  intro X Y f hf
  let := horn_weakFactorization.{u}
  let d := factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (anodyne_weak _ d.hi) (d.fac.symm ▸ hf.2)
  have hp : I.rlp d.p := GeometricRecognition.weak_fibration_rlp d.p d.hp hpw
  have hf' : I.rlp.llp f := boundary_left_class.symm ▸ hf.1
  have : HasLiftingProperty f d.p := hf' d.p hp
  exact SSet.anodyneExtensions.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.DependentPosets
open CategoryTheory Limits Opposite
attribute [-instance] CategoryTheory.Sigma.sigma

open Attachments AttachmentComparison
end Thomason.DependentPosets

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason

lemma boundaryImages_right_class {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (boundaryImages L).rlp = simplicialFibrations.inverseImage R ⊓
      simplicialWeakEquivalences.inverseImage R := by
  rw [boundaryImages_rlp adj, GeometricRecognition.boundary_right_class]
  rfl

lemma transferred_second_wfs {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    IsWeakFactorizationSystem
      (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R).llp
      (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R) := by
  rw [← boundaryImages_right_class adj]
  exact boundaryImages_weakFactorization L

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GeometricRecognition
open KanLocal KanHomotopy Subdivision
open SSet.modelCategoryQuillen

lemma weak_local {A B : SSet.{u}} (f : A ⟶ B) (hf : simplicialWeakEquivalences f) : Local f := by
  let := KanQuillen.horn_weakFactorization.{u}
  let d := MorphismProperty.factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (KanQuillen.anodyne_weak _ d.hi) (d.fac.symm ▸ hf)
  rw [← d.fac]
  exact local_comp (local_anodyne _ d.hi)
    (local_heq _ (heq_of_rlp _ (by rw [SSet.rlp_monomorphisms]; exact weak_fibration_rlp _ d.hp hpw)))

lemma weak_kan_heq {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : simplicialWeakEquivalences f) : IsHomotopyEquivalence f := by
  let := KanQuillen.horn_weakFactorization.{u}
  let d := MorphismProperty.factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (KanQuillen.anodyne_weak _ d.hi) (d.fac.symm ▸ hf)
  let : HomotopicalAlgebra.Fibration d.p := by
    rw [HomotopicalAlgebra.fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]; exact d.hp
  let : SSet.KanComplex d.Z := HomotopicalAlgebra.isFibrant_of_fibration d.p
  rw [← d.fac]
  exact heq_comp (heq_anodyne _ d.hi) (heq_of_rlp _ (by rw [SSet.rlp_monomorphisms]; exact weak_fibration_rlp _ d.hp hpw))

theorem left_proper : LeftProperFor simplicialWeakEquivalences.{u}
    (MorphismProperty.monomorphisms SSet) := by
  intro A B X Y i f g j sq hi hf
  let : Mono i := hi
  exact local_weak _ (local_pushout sq.flip (weak_local _ hf))

theorem right_proper : RightProperFor simplicialWeakEquivalences.{u}
    simplicialFibrations := by
  intro A B X Y f g p q sq hq hp
  apply (exInfinity_map_weak_iff g).mp
  let : SSet.KanComplex (exInfinityFunctor.obj B) := exInfinity_kan B
  let : SSet.KanComplex (exInfinityFunctor.obj Y) := exInfinity_kan Y
  exact homotopy_equivalence_weak _ (pullback_heq (sq.map exInfinityFunctor)
    (weak_kan_heq _ ((exInfinity_map_weak_iff p).mpr hp)) (exInfinity_fibration q hq))
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z


namespace Thomason.QuillenCriterion
open CategoryTheory
open Subdivision
lemma sdEx_unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences (SSet.sdExAdjunction.unit.app K) := by
  have h := exComparison_weak K
  change simplicialWeakEquivalences
    (SSet.sdExAdjunction.unit.app K ≫ SSet.ex.map (lastVertex.app K)) at h
  exact simplicialWeakEquivalences.of_postcomp _ _
    ((ex_map_weak_iff _).mpr (lastVertex_weak K)) h

lemma sdExSquared_unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences
      ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app K) := by
  change simplicialWeakEquivalences
    (SSet.sdExAdjunction.unit.app K ≫
      SSet.ex.map (SSet.sdExAdjunction.unit.app (SSet.sd.obj K)))
  exact simplicialWeakEquivalences.comp_mem _ _ (sdEx_unit_weak K)
    ((ex_map_weak_iff _).mpr (sdEx_unit_weak _))

end Thomason.QuillenCriterion

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason

lemma transferred_right_proper {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    RightProperFor (simplicialWeakEquivalences.inverseImage R)
      (simplicialFibrations.inverseImage R) := by
  let := adj.rightAdjoint_preservesLimits
  intro A B X Y f g p q sq hq hp
  exact GeometricRecognition.right_proper _ _ _ _ (sq.map R) hq hp

lemma left_preserves_cofibrations {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R)
    {K K' : SSet.{u}} (f : K ⟶ K') [Mono f] :
    (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R).llp
      (L.map f) := by
  intro A B p hp
  apply (adj.hasLiftingProperty_iff f p).mpr
  have h : SSet.modelCategoryQuillen.I.rlp (R.map p) := by
    rw [GeometricRecognition.boundary_right_class]
    exact hp
  rw [← SSet.rlp_monomorphisms] at h
  exact h f (show Mono f from inferInstance)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.BoundaryProperness

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GrayGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gray Generators. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

abbrev join (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) :=
  CellTerm.composeOrLeft C k x y

lemma join_eq (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) : C.join k x y = C.comp k x y h := by
  simp only [join, CellTerm.composeOrLeft, dite_eq_left h]

lemma join_source_le (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hik : i ≤ k) (h : C.target k x = C.source k y) :
    C.source i (C.join k x y) = C.source i x := by
  rw [C.join_eq k x y h, C.source_comp_le i k hik]

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ModelTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.SimplicialGluing
open CategoryTheory Limits MorphismProperty

lemma under_weak {C A B D P Q : SSet.{u}} (k : C ⟶ A) (i : C ⟶ B) (i' : C ⟶ D)
    [Mono i] [Mono i'] (f : B ⟶ D) (hf : simplicialWeakEquivalences f)
    (hif : i ≫ f = i') {a : A ⟶ P} {b : B ⟶ P} {a' : A ⟶ Q} {b' : D ⟶ Q}
    (s : IsPushout k i a b) (s' : IsPushout k i' a' b')
    (F : P ⟶ Q) (ha : a ≫ F = a') (hb : b ≫ F = f ≫ b') :
    simplicialWeakEquivalences F := by
  let E := pushout i i'
  let eB : B ⟶ E := pushout.inl i i'
  let eD : D ⟶ E := pushout.inr i i'
  let e : E ⟶ D := pushout.desc f (𝟙 D) (by simpa using hif)
  let := KanQuillen.boundary_weakFactorization.{u}
  let d := factorizationData (monomorphisms SSet) SSet.modelCategoryQuillen.I.rlp e
  have : Mono d.i := d.hi
  have hwp : simplicialWeakEquivalences d.p := KanQuillen.boundary_right_weak _ d.hp
  have : Mono eB := MorphismProperty.of_isPushout (IsPushout.of_hasPushout i i')
    (show (monomorphisms SSet) i' from inferInstance)
  have : Mono eD := MorphismProperty.of_isPushout (IsPushout.of_hasPushout i i').flip
    (show (monomorphisms SSet) i from inferInstance)
  let u : B ⟶ d.Z := eB ≫ d.i
  let v : D ⟶ d.Z := eD ≫ d.i
  have hup : u ≫ d.p = f := by
    rw [show u = eB ≫ d.i from rfl, Category.assoc, d.fac]
    exact pushout.inl_desc _ _ _
  have hvp : v ≫ d.p = 𝟙 D := by
    rw [show v = eD ≫ d.i from rfl, Category.assoc, d.fac]
    exact pushout.inr_desc _ _ _
  have hu : SSet.anodyneExtensions u := by
    rw [KanQuillen.anodyne_class]
    exact ⟨show Mono u from inferInstance, simplicialWeakEquivalences.of_postcomp u d.p hwp (hup ▸ hf)⟩
  have hv : SSet.anodyneExtensions v := by
    rw [KanQuillen.anodyne_class]
    exact ⟨show Mono v from inferInstance, simplicialWeakEquivalences.of_postcomp v d.p hwp
      (hvp ▸ simplicialWeakEquivalences.id_mem D)⟩
  let h := i ≫ u
  have hh : h = i' ≫ v := by
    dsimp [h,u,v,eB,eD]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  let H := pushout k h
  let x : A ⟶ H := pushout.inl k h
  let z : d.Z ⟶ H := pushout.inr k h
  have sh : IsPushout k h x z := IsPushout.of_hasPushout k h
  let U : P ⟶ H := s.desc x (u ≫ z) (by
    rw [← Category.assoc]; exact sh.w)
  let V : Q ⟶ H := s'.desc x (v ≫ z) (by
    rw [← Category.assoc, ← hh]; exact sh.w)
  have hUa : a ≫ U = x := s.inl_desc _ _ _
  have hUb : b ≫ U = u ≫ z := s.inr_desc _ _ _
  have hVa : a' ≫ V = x := s'.inl_desc _ _ _
  have hVb : b' ≫ V = v ≫ z := s'.inr_desc _ _ _
  have su : IsPushout b u U z := by
    have st : IsPushout k (i ≫ u) (a ≫ U) z := by rw [hUa]; exact sh
    exact st.of_top hUb s
  have sv : IsPushout b' v V z := by
    have st : IsPushout k (i' ≫ v) (a' ≫ V) z := by rw [hVa, ← hh]; exact sh
    exact st.of_top hVb s'
  have hwU : simplicialWeakEquivalences U :=
    KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout su hu)
  have hwV : simplicialWeakEquivalences V :=
    KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sv hv)
  let R : H ⟶ Q := sh.desc a' (d.p ≫ b') (by
    rw [← Category.assoc]
    change k ≫ a' = ((i ≫ u) ≫ d.p) ≫ b'
    rw [Category.assoc i, hup, hif]
    exact s'.w)
  have hxR : x ≫ R = a' := sh.inl_desc _ _ _
  have hzR : z ≫ R = d.p ≫ b' := sh.inr_desc _ _ _
  have hVR : V ≫ R = 𝟙 Q := by
    apply s'.hom_ext
    · rw [← Category.assoc, hVa, hxR, Category.comp_id]
    · rw [← Category.assoc, hVb, Category.assoc, hzR, ← Category.assoc, hvp,
        Category.id_comp, Category.comp_id]
  have hUR : U ≫ R = F := by
    apply s.hom_ext
    · rw [← Category.assoc, hUa, hxR, ha]
    · rw [← Category.assoc, hUb, Category.assoc, hzR, ← Category.assoc, hup, hb]
  have hwR : simplicialWeakEquivalences R :=
    simplicialWeakEquivalences.of_precomp V R hwV (hVR ▸ simplicialWeakEquivalences.id_mem Q)
  rw [← hUR]
  exact simplicialWeakEquivalences.comp_mem _ _ hwU hwR

lemma span_weak {C C' A A' B B' P Q : SSet.{u}}
    (k : C ⟶ A) (i : C ⟶ B) (k' : C' ⟶ A') (i' : C' ⟶ B')
    [Mono i] [Mono i'] (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (ha : simplicialWeakEquivalences a) (hb : simplicialWeakEquivalences b)
    (hc : simplicialWeakEquivalences c) (hk : k ≫ a = c ≫ k') (hi : i ≫ b = c ≫ i')
    {lA : A ⟶ P} {lB : B ⟶ P} {lA' : A' ⟶ Q} {lB' : B' ⟶ Q}
    (s : IsPushout k i lA lB) (s' : IsPushout k' i' lA' lB')
    (F : P ⟶ Q) (hFA : lA ≫ F = a ≫ lA') (hFB : lB ≫ F = b ≫ lB') :
    simplicialWeakEquivalences F := by
  let E := pushout i c
  let j : B ⟶ E := pushout.inl i c
  let e : C' ⟶ E := pushout.inr i c
  have se : IsPushout i c j e := IsPushout.of_hasPushout i c
  have : Mono e := MorphismProperty.of_isPushout se.flip
    (show (monomorphisms SSet) i from inferInstance)
  have hwj : simplicialWeakEquivalences j :=
    GeometricRecognition.left_proper _ _ _ _ se inferInstance hc
  let t : E ⟶ B' := se.desc b i' hi
  have htB : j ≫ t = b := se.inl_desc _ _ _
  have htC : e ≫ t = i' := se.inr_desc _ _ _
  have hwt : simplicialWeakEquivalences t :=
    simplicialWeakEquivalences.of_precomp j t hwj (htB ▸ hb)
  let H := pushout (k ≫ a) i
  let x : A' ⟶ H := pushout.inl (k ≫ a) i
  let y : B ⟶ H := pushout.inr (k ≫ a) i
  have sh : IsPushout (k ≫ a) i x y := IsPushout.of_hasPushout (k ≫ a) i
  let U : P ⟶ H := s.desc (a ≫ x) y (by rw [← Category.assoc]; exact sh.w)
  have hUA : lA ≫ U = a ≫ x := s.inl_desc _ _ _
  have hUB : lB ≫ U = y := s.inr_desc _ _ _
  have hwU : simplicialWeakEquivalences U := KanLocal.local_weak _
    (KanLocal.local_pushout_map k i a (GeometricRecognition.weak_local _ ha) s sh U hUA hUB)
  let z : E ⟶ H := se.desc y (k' ≫ x) (by
    rw [← sh.w, hk, Category.assoc])
  have hzB : j ≫ z = y := se.inl_desc _ _ _
  have hzC : e ≫ z = k' ≫ x := se.inr_desc _ _ _
  have sh' : IsPushout k' e x z := by
    have sr : IsPushout i (c ≫ k') (j ≫ z) x := by rw [← hk,hzB]; exact sh.flip
    exact (sr.of_top hzC se).flip
  let V : H ⟶ Q := sh'.desc lA' (t ≫ lB') (by rw [← Category.assoc, htC]; exact s'.w)
  have hVA : x ≫ V = lA' := sh'.inl_desc _ _ _
  have hVE : z ≫ V = t ≫ lB' := sh'.inr_desc _ _ _
  have hwV : simplicialWeakEquivalences V := under_weak k' e i' t hwt htC sh' s' V hVA hVE
  have hUV : U ≫ V = F := by
    apply s.hom_ext
    · rw [← Category.assoc, hUA, Category.assoc, hVA, hFA]
    · rw [← Category.assoc, hUB, ← hzB, Category.assoc, hVE, ← Category.assoc, htB, hFB]
  rw [← hUV]
  exact simplicialWeakEquivalences.comp_mem _ _ hwU hwV

end Thomason.SimplicialGluing

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty Simplicial
open Attachments
open AttachmentComparison (upward nerve_mono_orderMap)

variable {C : Type v} [Category.{u} C]

lemma weak_iff_nerve (N : C ⥤ SSet.{u}) {X Y : C} (f : X ⟶ Y) :
    W N f ↔ simplicialWeakEquivalences (N.map f) :=
  Subdivision.exSquared_map_weak_iff (N.map f)

variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable (h : PosetComparison G N adj)
include h

lemma unit_local_initial {X : SSet.{u}} (hX : IsInitial X) : KanLocal.Local (adj.unit.app X) := by
  let P := ULift.{u} Empty
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  exact unit_local_of_iso (hP.uniqueUpToIso hX)
    (GeometricRecognition.weak_local _ (h.unit_weak P))

variable [PreservesColimitsOfSize.{u,u} G]

lemma unit_local_attachment {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A) (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {V Y : SSet.{u}} (a : nerve A ⟶ V) (j : V ⟶ Y) (v : nerve B ⟶ Y)
    (sc : IsPushout a (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) j v)
    (hV : KanLocal.Local (adj.unit.app V)) : KanLocal.Local (adj.unit.app Y) := by
  let i : nerve A ⟶ nerve B :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have : Mono i := nerve_mono_orderMap (A := A) (E := B)
    (OrderEmbedding.subtype A).toOrderHom Subtype.val_injective
  let b := N.map (G.map a)
  let c := N.map (G.map i)
  have : Mono c := inc_mono h A hA
  let P := pushout b c
  let lV := pushout.inl b c
  let lB := pushout.inr b c
  have ss : IsPushout b c lV lB := IsPushout.of_hasPushout b c
  have hna : a ≫ adj.unit.app V = adj.unit.app (nerve A) ≫ b := adj.unit.naturality a
  have hni : i ≫ adj.unit.app (nerve B) = adj.unit.app (nerve A) ≫ c := adj.unit.naturality i
  let q : Y ⟶ P := sc.desc (adj.unit.app V ≫ lV) (adj.unit.app (nerve B) ≫ lB) (by
    change a ≫ adj.unit.app V ≫ lV = i ≫ adj.unit.app (nerve B) ≫ lB
    rw [← Category.assoc, hna, Category.assoc, ss.w,
      ← Category.assoc, ← hni, Category.assoc])
  have hqV : j ≫ q = adj.unit.app V ≫ lV := sc.inl_desc _ _ _
  have hqB : v ≫ q = adj.unit.app (nerve B) ≫ lB := sc.inr_desc _ _ _
  have hq : simplicialWeakEquivalences q := SimplicialGluing.span_weak a i b c
    (adj.unit.app V) (adj.unit.app (nerve B)) (adj.unit.app (nerve A))
    (KanLocal.local_weak _ hV) (h.unit_weak B) (h.unit_weak A)
    (adj.unit.naturality a) (adj.unit.naturality i) sc ss q hqV hqB
  have cs : IsPushout (G.map a) (inc G A) (G.map j) (G.map v) := sc.map G
  let t : P ⟶ N.obj (G.obj Y) := ss.desc (N.map (G.map j)) (N.map (G.map v)) (by
    dsimp [b,c]
    rw [← N.map_comp, ← N.map_comp]
    exact congrArg N.map cs.w)
  have htV : lV ≫ t = N.map (G.map j) := ss.inl_desc _ _ _
  have htB : lB ≫ t = N.map (G.map v) := ss.inr_desc _ _ _
  have ht : simplicialWeakEquivalences t := h.comparison A hA r hadj (G.map a)
    (G.map j) (G.map v) cs ss t htV htB
  have hqt : q ≫ t = adj.unit.app Y := by
    apply sc.hom_ext
    · rw [← Category.assoc,hqV,Category.assoc,htV]
      exact (adj.unit.naturality j).symm
    · rw [← Category.assoc,hqB,Category.assoc,htB]
      exact (adj.unit.naturality v).symm
  apply GeometricRecognition.weak_local
  rw [← hqt]
  exact simplicialWeakEquivalences.comp_mem _ _ hq ht

open PartialOrder HornAttachments KanLocal
open SubdividedUnit (D Flags BoundaryFlags boundaryCoprodIso simplexCoprodIso boundaryCoprodIso_naturality)

lemma boundary_unit_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : Local (adj.unit.app (D.obj X))) :
    Local (adj.unit.app (D.obj Y)) ∧ Mono (D.map j) ∧ Mono (N.map (G.map (D.map j))) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hrA : ∀ a : A, rA ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
    PosetCoproduct.oldRetraction_retract I _ _ (flagRetraction_retract _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  have : Mono i := nerve_mono_orderMap (A := A) (E := PosetCoproduct.Piece I (Flags d))
    (OrderEmbedding.subtype A).toOrderHom Subtype.val_injective
  refine ⟨unit_local_attachment h A hA rA hadj a' (D.map j) v' sq hX,
    Adhesive.mono_of_isPushout_of_mono_right sq, ?_⟩
  exact h.attachment_mono A hA (G.map a') (G.map (D.map j)) (G.map v') (sq.map G)

lemma unit_local_skeleton (K : SSet.{u}) (d : ℕ) :
    Local (adj.unit.app (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply unit_local_initial h
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact (boundary_unit_successor h
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
      ih).1

lemma skeleton_monos (K : SSet.{u}) (d : ℕ) :
    Mono (D.map ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))) ∧
      Mono (N.map (G.map (D.map
        ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))))) :=
  (boundary_unit_successor h
    (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
    (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
    (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
    (unit_local_skeleton h K d)).2

variable [PreservesFilteredColimitsOfSize.{u,u} N]

theorem subdivided_unit_local (K : SSet.{u}) : Local (adj.unit.app (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D
  let H := c.F ⋙ D ⋙ G ⋙ N
  let f : F ⟶ H := Functor.whiskerLeft F adj.unit
  have hf : Local (colim.map f) := local_colimit_nat F H f
    (fun d => (skeleton_monos h K d).1) (fun d => (skeleton_monos h K d).2)
    (unit_local_skeleton h K)
  have hcF : IsColimit (D.mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves D c.isColimit
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  let : PreservesColimitsOfSize.{0,0} G := preservesSmallestColimits_of_preservesColimits G
  have hcG : IsColimit ((D ⋙ G ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ G ⋙ N) c.isColimit
  let eF : D.obj K ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj (G.obj (D.obj K)) ≅ colimit H :=
    hcG.coconePointUniqueUpToIso (colimit.isColimit H)
  have hF (d : ℕ) : D.map (c.incl.app d) ≫ eF.hom = colimit.ι F d :=
    hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) d
  have hG (d : ℕ) : colimit.ι H d ≫ eG.inv = N.map (G.map (D.map (c.incl.app d))) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit H) d
  have he : adj.unit.app (D.obj K) = eF.hom ≫ colim.map f ≫ eG.inv := by
    apply hcF.hom_ext
    intro d
    change D.map (c.incl.app d) ≫ adj.unit.app (D.obj K) =
      D.map (c.incl.app d) ≫ eF.hom ≫ colim.map f ≫ eG.inv
    rw [← Category.assoc, hF, ← Category.assoc, colimit.ι_map, Category.assoc, hG]
    exact adj.unit.naturality (D.map (c.incl.app d))
  rw [he]
  exact local_comp (local_iso _) (local_comp hf (local_iso _))

end Thomason.AbstractTransfer

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Horns
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open TransferAcyclicity (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma horn_admissible : hornImages (L G) ≤ Admissible G := by
  rintro X Y f hf
  simp only [hornImages, MorphismProperty.iSup_iff] at hf
  obtain ⟨m,⟨k⟩⟩ := hf
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+2))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.horn (m+1) k))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _
    anodyne := by
      exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
        (oldFlagsIso (SSet.horn (m+1) k)) (Subdivision.sdTwiceSimplexIso (m+1))
        (oldFlagsIso_naturality (SSet.horn (m+1) k)).symm)).mp
          (HornSubdivision.sdTwice_horn_anodyne (by omega) k) }
  refine ⟨d, ⟨(Arrow.isoMk (G.mapIso (oldFlagsIso (SSet.horn (m+1) k)))
    (G.mapIso (Subdivision.sdTwiceSimplexIso (m+1))) ?_).symm⟩⟩
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg G.map (oldFlagsIso_naturality (SSet.horn (m+1) k)).symm

variable (h : PosetComparison G N adj)
include h

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma poset_attachment_local (d : PosetAttachment.{u})
    {X Y : C} (a : posetObj G d.A ⟶ X)
    (j : X ⟶ Y) (v : posetObj G d.B ⟶ Y) (sc : IsPushout a (inc G d.A) j v) :
    Local (N.map j) ∧ Mono (N.map j) := by
  let b := N.map a
  let i := N.map (inc G d.A)
  let ss := IsPushout.of_hasPushout b i
  let F : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  have hFX : pushout.inl b i ≫ F = N.map j := ss.inl_desc _ _ _
  have hFB : pushout.inr b i ≫ F = N.map v := ss.inr_desc _ _ _
  have hF := GeometricRecognition.weak_local F
    (h.comparison d.A d.lower d.retraction d.adjunction a j v sc ss F hFX hFB)
  have hi : SSet.anodyneExtensions i := by
    have hmono : Mono i := inc_mono h d.A d.lower
    rw [KanQuillen.anodyne_class]
    refine ⟨hmono, ?_⟩
    refine simplicialWeakEquivalences.of_precomp (W' := simplicialWeakEquivalences)
      (adj.unit.app (nerve d.A)) i (h.unit_weak d.A) ?_
    let inclusion : nerve d.A ⟶ nerve d.B :=
      nerveMap (OrderEmbedding.subtype d.A).toOrderHom.toFunctor
    have naturality : inclusion ≫ adj.unit.app (nerve d.B) =
        adj.unit.app (nerve d.A) ≫ i := adj.unit.naturality inclusion
    rw [← naturality]
    exact simplicialWeakEquivalences.comp_mem _ _
      (KanQuillen.anodyne_weak _ d.anodyne) (h.unit_weak d.B)
  refine ⟨?_,h.attachment_mono d.A d.lower a j v sc⟩
  rw [← hFX]
  exact local_comp (local_anodyne _ (SSet.anodyneExtensions.of_isPushout ss hi)) hF

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout {A B X Y : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Local (N.map j) ∧ Mono (N.map j) := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact poset_attachment_local h d _ _ _ sq

lemma coproduct_horn_pushout {X Y : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (hornImages (L G))).pushouts j) :
    Local (N.map j) ∧ Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone horn_admissible _ hi))
    a j v sc

end Thomason.AbstractTransfer.Horns

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open KanLocal SubdividedUnit Horns
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

lemma sequential_horn_weak {X Y : C} (f : X ⟶ Y)
    (ht : (MorphismProperty.coproducts.{u} (hornImages (L G))).pushouts.TransfiniteCompositionOfShape ℕ f) : W N f := by
  let G := ht.F ⋙ N
  let F := (Functor.const ℕ).obj (G.obj 0)
  let a : F ⟶ G := {
    app n := G.map (homOfLE (Nat.zero_le n))
    naturality i j u := by
      change 𝟙 (G.obj 0) ≫ G.map _ = G.map _ ≫ G.map u
      rw [Category.id_comp, ← G.map_comp]
      rfl }
  have hG (n : ℕ) : Local (G.map (homOfLE (Nat.le_succ n))) ∧
      Mono (G.map (homOfLE (Nat.le_succ n))) :=
    coproduct_horn_pushout h _ (ht.map_mem n (by simp))
  have ha (n : ℕ) : Local (a.app n) := by
    induction n with
    | zero =>
      change Local (G.map (𝟙 0))
      rw [G.map_id]
      exact local_iso _
    | succ n ih =>
      have he : a.app (n+1) = a.app n ≫ G.map (homOfLE (Nat.le_succ n)) := by
        change G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp]
        rfl
      rw [he]
      exact local_comp ih (hG n).1
  have hl := local_colimit_nat F G a (fun n => by dsimp [F]; infer_instance)
    (fun n => (hG n).2) ha
  have hcF : IsColimit (constCocone ℕ (G.obj 0)) := isColimitConstCocone _ _
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcG : IsColimit (N.mapCocone { pt := Y, ι := ht.incl }) :=
    isColimitOfPreserves N ht.isColimit
  let eF : G.obj 0 ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj Y ≅ colimit G := hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have eFι : eF.hom = colimit.ι F 0 := by
    exact (Category.id_comp eF.hom).symm.trans
      (hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) 0)
  have eGι : colimit.ι G 0 ≫ eG.inv = N.map (ht.incl.app 0) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit G) 0
  have he : N.map (ht.incl.app 0) = eF.hom ≫ colim.map a ≫ eG.inv := by
    rw [eFι, ← Category.assoc, colimit.ι_map, Category.assoc, eGι]
    change _ = G.map (𝟙 0) ≫ _
    rw [G.map_id, Category.id_comp]
  apply (weak_iff_nerve N f).mpr
  apply local_weak
  rw [← ht.fac, N.map_comp]
  change Local (N.map ht.isoBot.inv ≫ N.map (ht.incl.app 0))
  rw [he]
  exact local_comp (local_iso _) (local_comp (local_iso _) (local_comp hl (local_iso _)))

theorem horn_acyclicity [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}] :
    (hornImages (L G)).rlp.llp ≤ W N := by
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]
  rintro X Y f ⟨A,B,g,r,⟨hh⟩⟩
  exact (W N).of_retract r (sequential_horn_weak h g hh)

variable [IsLocallyPresentable.{u} C]
variable [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}]

lemma first_left_class : (Fib N).llp = Cof N ⊓ W N := by
  have hc : (Fib N).llp ≤ Cof N := fun _ _ _ hi _ _ p hp => hi p hp.1
  have hw : (Fib N).llp ≤ W N := by
    have hh := horn_acyclicity h
    rwa [hornImages_rlp (transferredAdjunction adj)] at hh
  apply le_antisymm (le_inf hc hw)
  intro X Y f hf
  have := first_wfs_aux (G := G) (adj := adj)
  let d := factorizationData (Fib N).llp (Fib N) f
  have hpw : W N d.p := (W N).of_precomp d.i d.p (hw _ d.hi) (d.fac.symm ▸ hf.2)
  have : HasLiftingProperty f d.p := hf.1 d.p ⟨d.hp,hpw⟩
  exact (Fib N).llp.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

theorem first_wfs : IsWeakFactorizationSystem (Cof N ⊓ W N) (Fib N) := by
  rw [← first_left_class h]
  exact first_wfs_aux (G := G) (adj := adj)

variable [HasLimitsOfSize.{u,u} C]

@[instance_reducible] def model : ModelCategory C := by
  letI : CategoryWithWeakEquivalences C := ⟨W N⟩
  letI : CategoryWithFibrations C := ⟨Fib N⟩
  letI : CategoryWithCofibrations C := ⟨Cof N⟩
  letI : (weakEquivalences C).HasTwoOutOfThreeProperty :=
    show (W N).HasTwoOutOfThreeProperty from inferInstance
  letI : IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) := first_wfs h
  letI : IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) :=
    transferred_second_wfs (transferredAdjunction adj)
  exact ModelCategory.mk' _

end Thomason.AbstractTransfer

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ProperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open BoundaryProperness (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma boundary_admissible : boundaryImages (L G) ≤ Admissible G := by
  rintro X Y f ⟨m⟩
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+1))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.boundary m))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _ }
  refine ⟨d, ⟨(Arrow.isoMk (G.mapIso (oldFlagsIso (SSet.boundary m)))
    (G.mapIso (Subdivision.sdTwiceSimplexIso m)) ?_).symm⟩⟩
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg G.map (oldFlagsIso_naturality (SSet.boundary m)).symm

variable (h : PosetComparison G N adj)
include h

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma poset_attachment_invariance (d : PosetAttachment.{u})
    {X Y X' Y' : C}
    (a : posetObj G d.A ⟶ X) (j : X ⟶ Y) (v : posetObj G d.B ⟶ Y)
    (sc : IsPushout a (inc G d.A) j v)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y') (v' : posetObj G d.B ⟶ Y')
    (sc' : IsPushout (a ≫ f) (inc G d.A) j' v')
    (hj : j ≫ g = f ≫ j') (hv : v ≫ g = v')
    (hf : W N f) : W N g := by
  let b := N.map a
  let i := N.map (inc G d.A)
  have : Mono i := inc_mono h d.A d.lower
  let ss := IsPushout.of_hasPushout b i
  let ss' := IsPushout.of_hasPushout (b ≫ N.map f) i
  let t : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  let t' : pushout (b ≫ N.map f) i ⟶ N.obj Y' := ss'.desc (N.map j') (N.map v') (by
    rw [← N.map_comp, ← N.map_comp, ← N.map_comp, sc'.w])
  have ht := GeometricRecognition.weak_local t
    (h.comparison d.A d.lower d.retraction d.adjunction a j v
      sc ss t (ss.inl_desc _ _ _) (ss.inr_desc _ _ _))
  have ht' := GeometricRecognition.weak_local t'
    (h.comparison d.A d.lower d.retraction d.adjunction (a ≫ f) j' v'
      sc' (by simpa [b,Functor.map_comp] using ss') t' (ss'.inl_desc _ _ _) (ss'.inr_desc _ _ _))
  let s : pushout b i ⟶ pushout (b ≫ N.map f) i :=
    ss.desc (N.map f ≫ pushout.inl (b ≫ N.map f) i) (pushout.inr (b ≫ N.map f) i)
      (by simpa [Category.assoc] using ss'.w)
  have hs : Local s := local_pushout_map b i (N.map f)
    (GeometricRecognition.weak_local _ ((weak_iff_nerve N f).mp hf))
    ss ss' s (ss.inl_desc _ _ _) (ss.inr_desc _ _ _)
  have he : t ≫ N.map g = s ≫ t' := by
    apply ss.hom_ext
    · dsimp [t,s,t']
      simp only [IsPushout.inl_desc_assoc,Category.assoc,IsPushout.inl_desc]
      rw [← N.map_comp, ← N.map_comp, hj]
    · dsimp [t,s,t']
      simp only [IsPushout.inr_desc_assoc,IsPushout.inr_desc]
      rw [← N.map_comp,hv]
  apply (weak_iff_nerve N g).mpr
  apply simplicialWeakEquivalences.of_precomp t _ (local_weak t ht)
  rw [he]
  exact local_weak _ (local_comp hs ht')

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout_mono {A B X Y : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Mono (N.map j) := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact h.attachment_mono d.A d.lower _ _ _ sq

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout_weak {A B X Y X' Y' : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : W N f) :
    W N g := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq₀ : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact poset_attachment_invariance h d _ _ _ sq₀ f g j' _
    (sq₀.flip.paste_vert sq).flip sq.w rfl hf

lemma coproduct_boundary_pushout_mono {X Y : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (L G))).pushouts j) : Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_mono h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc

lemma coproduct_boundary_pushout_weak {X Y X' Y' : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (L G))).pushouts j)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : W N f) :
    W N g := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_weak h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc f g j' sq hf

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits MorphismProperty
open KanLocal SubdividedUnit

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

abbrev Cells (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  (MorphismProperty.coproducts.{u} (boundaryImages (L G))).pushouts

lemma sequential_pushout_weak {X Y X' : C}
    (i : X ⟶ Y) (ht : (Cells G).TransfiniteCompositionOfShape ℕ i)
    (f : X ⟶ X') (hf : W N f) :
    W N (pushout.inl i f) := by
  let K := G
  let F := ht.F
  let a : (Functor.const ℕ).obj X ⟶ F := {
    app n := ht.isoBot.inv ≫ F.map (homOfLE (Nat.zero_le n))
    naturality n m u := by
      change 𝟙 X ≫ (ht.isoBot.inv ≫ F.map _) = (ht.isoBot.inv ≫ F.map _) ≫ F.map u
      rw [Category.id_comp,Category.assoc,← F.map_comp]
      rfl }
  have ha (n m : ℕ) (u : n ⟶ m) : a.app n ≫ F.map u = a.app m := by
    simpa using (a.naturality u).symm
  let U := Under.lift F a
  let G := U ⋙ CategoryTheory.Under.pushout f ⋙ Under.forget X'
  let e : F ⟶ G := {
    app n := pushout.inl (a.app n) f
    naturality n m u := by
      simp [G,U,CategoryTheory.Under.pushout,Under.lift,pushout.inl_desc] }
  have sq (n m : ℕ) (u : n ⟶ m) :
      IsPushout (F.map u) (e.app n) (e.app m) (G.map u) := by
    have sb : IsPushout (a.app n ≫ F.map u) f (e.app m)
        (pushout.inr (a.app n) f ≫ G.map u) := by
      have hg : pushout.inr (a.app n) f ≫ G.map u = pushout.inr (a.app m) f := by
        simp [G,U,CategoryTheory.Under.pushout,Under.lift,pushout.inr_desc]
      rw [hg, ha n m u]
      exact IsPushout.of_hasPushout _ _
    exact sb.of_left (e.naturality u) (IsPushout.of_hasPushout _ _)
  have hF (n : ℕ) : Cells K (F.map (homOfLE (Nat.le_succ n))) := ht.map_mem n (by simp)
  have hG (n : ℕ) : Cells K (G.map (homOfLE (Nat.le_succ n))) :=
    MorphismProperty.of_isPushout (sq n (n+1) (homOfLE (Nat.le_succ n))).flip (hF n)
  have he (n : ℕ) : W N (e.app n) := by
    induction n with
    | zero =>
      have : IsIso (a.app 0) := by
        change IsIso (ht.isoBot.inv ≫ F.map (𝟙 0))
        infer_instance
      have : IsIso (pushout.inr (a.app 0) f) := by infer_instance
      apply (W N).of_precomp (a.app 0) _
        (weak_iso (N := N) _)
      change W N (a.app 0 ≫ pushout.inl (a.app 0) f)
      rw [pushout.condition]
      exact (W N).comp_mem _ _ hf
        (weak_iso (N := N) _)
    | succ n ih =>
      exact coproduct_boundary_pushout_weak h _ (hF n) _ _ _
        (sq n (n+1) (homOfLE (Nat.le_succ n))) ih
  have hp (n : ℕ) : a.app n ≫ ht.incl.app n = i := by
    dsimp [a]
    rw [Category.assoc]
    have hn := ht.incl.naturality (homOfLE (Nat.zero_le n))
    dsimp at hn
    rw [hn,Category.comp_id]
    exact ht.fac
  let cU := Under.liftCocone F a ⟨Y,ht.incl⟩ i hp
  have hcU : IsColimit cU := Under.isColimitLiftCocone F a _ i hp ht.isColimit
  let cG := (Under.forget X').mapCocone ((CategoryTheory.Under.pushout f).mapCocone cU)
  have hcG : IsColimit cG := isColimitOfPreserves _ (isColimitOfPreserves _ hcU)
  let FN := F ⋙ N
  let GN := G ⋙ N
  let eN : FN ⟶ GN := Functor.whiskerRight e N
  have hn : Local (colim.map eN) := local_colimit_nat FN GN eN
    (fun n => coproduct_boundary_pushout_mono h _ (hF n))
    (fun n => coproduct_boundary_pushout_mono h _ (hG n))
    (fun n => GeometricRecognition.weak_local _
      ((weak_iff_nerve N (e.app n)).mp (he n)))
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcFN : IsColimit (N.mapCocone ⟨Y,ht.incl⟩) := isColimitOfPreserves N ht.isColimit
  have hcGN : IsColimit (N.mapCocone cG) := isColimitOfPreserves N hcG
  let eF : N.obj Y ≅ colimit FN := hcFN.coconePointUniqueUpToIso (colimit.isColimit FN)
  let eG : N.obj (pushout i f) ≅ colimit GN :=
    hcGN.coconePointUniqueUpToIso (colimit.isColimit GN)
  have eFι (n : ℕ) : N.map (ht.incl.app n) ≫ eF.hom = colimit.ι FN n :=
    hcFN.comp_coconePointUniqueUpToIso_hom (colimit.isColimit FN) n
  have eGι (n : ℕ) : colimit.ι GN n ≫ eG.inv = N.map (cG.ι.app n) :=
    hcGN.comp_coconePointUniqueUpToIso_inv (colimit.isColimit GN) n
  have eqn : N.map (pushout.inl i f) = eF.hom ≫ colim.map eN ≫ eG.inv := by
    apply hcFN.hom_ext
    intro n
    change N.map (ht.incl.app n) ≫ _ = N.map (ht.incl.app n) ≫ _
    rw [← Category.assoc, ← Category.assoc,
      eFι n, colimit.ι_map, Category.assoc, eGι n]
    change N.map (ht.incl.app n) ≫ N.map (pushout.inl i f) =
      N.map (e.app n) ≫ N.map (cG.ι.app n)
    rw [← N.map_comp, ← N.map_comp]
    congr 1
    simp [e,cG,cU,CategoryTheory.Under.pushout,Under.lift,Under.liftCocone]
    exact (pushout.inl_desc _ _ _).symm
  apply (weak_iff_nerve N _).mpr
  rw [eqn]
  exact local_weak _ (local_comp (local_iso _) (local_comp hn (local_iso _)))

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable [IsCardinalForSmallObjectArgument (boundaryImages (L G)) Cardinal.aleph0.{u}]

lemma cofibration_pushout_weak {X Y X' : C}
    (i : X ⟶ Y) (hi : Cof N i)
    (f : X ⟶ X') (hf : W N f) :
    W N (pushout.inl i f) := by
  let I := boundaryImages (L G)
  let κ := Cardinal.aleph0.{u}
  let k := SmallObject.ιObj I κ i
  let p := SmallObject.πObj I κ i
  have hp : Fib N p ∧ W N p := by
    have h := SmallObject.rlp_πObj I κ i
    change (boundaryImages (L G)).rlp p at h
    rw [boundaryImages_right_class (transferredAdjunction adj)] at h
    exact h
  have : HasLiftingProperty i p := hi p hp
  have fac : k ≫ p = i := SmallObject.ιObj_πObj I κ i
  let sq : CommSq k i p (𝟙 Y) := ⟨by simpa using fac⟩
  let s := sq.lift
  have hs : i ≫ s = k := sq.fac_left
  have hs' : s ≫ p = 𝟙 Y := sq.fac_right
  have hk : Nonempty ((Cells G).TransfiniteCompositionOfShape ℕ k) := by
    let e : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType := ULift.orderIso.{u}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
    have h := SmallObject.transfiniteCompositionsOfShape_ιObj I κ i
    rw [← MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e] at h
    exact h
  have hw : W N (pushout.inl k f) :=
    sequential_pushout_weak h k hk.some f hf
  let s' : pushout i f ⟶ pushout k f :=
    pushout.desc (s ≫ pushout.inl k f) (pushout.inr k f) (by
      rw [← Category.assoc,hs,pushout.condition])
  let p' : pushout k f ⟶ pushout i f :=
    pushout.desc (p ≫ pushout.inl i f) (pushout.inr i f) (by
      rw [← Category.assoc,fac,pushout.condition])
  have hsp : s' ≫ p' = 𝟙 (pushout i f) := by
    apply pushout.hom_ext
    · dsimp [s',p']
      simp only [pushout.inl_desc_assoc,Category.assoc,pushout.inl_desc,Category.comp_id]
      rw [← Category.assoc,hs',Category.id_comp]
    · dsimp [s',p']
      simp only [pushout.inr_desc_assoc,pushout.inr_desc,Category.comp_id]
  let r : RetractArrow (pushout.inl i f) (pushout.inl k f) := {
    i := Arrow.homMk s s' (by simp [s',pushout.inl_desc])
    r := Arrow.homMk p p' (by simp [p',pushout.inl_desc])
    retract := by
      apply Arrow.hom_ext
      · exact hs'
      · exact hsp }
  exact (W N).of_retract r hw

theorem left_proper : LeftProperFor (W N)
    (Cof N) := by
  intro A B X Y i f g j sq hi hf
  rw [← sq.inl_isoPushout_inv]
  exact (W N).comp_mem _ _
    (cofibration_pushout_weak h i hi f hf)
    (weak_iso (N := N) _)

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {C : Type v} [Category.{u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

lemma unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences ((transferredAdjunction adj).unit.app K) := by
  change simplicialWeakEquivalences
    ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app K ≫
      (SSet.ex ⋙ SSet.ex).map (adj.unit.app ((SSet.sd ⋙ SSet.sd).obj K)))
  exact simplicialWeakEquivalences.comp_mem _ _ (QuillenCriterion.sdExSquared_unit_weak K)
    ((Subdivision.exSquared_map_weak_iff _).mpr
      (KanLocal.local_weak _ (subdivided_unit_local h K)))

theorem adjoint_weak_iff (K : SSet.{u}) (Y : C) (f : (L G).obj K ⟶ Y) :
    W N f ↔ simplicialWeakEquivalences ((transferredAdjunction adj).homEquiv K Y f) := by
  change simplicialWeakEquivalences ((R N).map f) ↔
    simplicialWeakEquivalences ((transferredAdjunction adj).unit.app K ≫ (R N).map f)
  constructor
  · exact simplicialWeakEquivalences.comp_mem _ _ (unit_weak h K)
  · exact simplicialWeakEquivalences.of_precomp _ _ (unit_weak h K)

lemma left_preserves_weak {K K' : SSet.{u}} (f : K ⟶ K')
    (hf : simplicialWeakEquivalences f) : W N ((L G).map f) := by
  apply simplicialWeakEquivalences.of_precomp
    ((transferredAdjunction adj).unit.app K) _ (unit_weak h K)
  change simplicialWeakEquivalences
    ((transferredAdjunction adj).unit.app K ≫ (L G ⋙ R N).map f)
  rw [← (transferredAdjunction adj).unit.naturality f]
  exact simplicialWeakEquivalences.comp_mem _ _ hf (unit_weak h K')

variable [HasLimitsOfSize.{u,u} C] [HasColimitsOfSize.{u,u} C]
variable [IsLocallyPresentable.{u} C]
variable [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}]
variable [IsCardinalForSmallObjectArgument (boundaryImages (L G)) Cardinal.aleph0.{u}]

def exactEndpoint : ExactModelEndpoint (L G) (R N) (transferredAdjunction adj) where
  model := model h
  weak_eq := rfl
  fib_eq := rfl
  cof_eq := rfl
  generating_cofibrations := boundaryImages_right_class (transferredAdjunction adj)
  generating_trivial_cofibrations := hornImages_rlp (transferredAdjunction adj)
  weak_factorization_one := first_wfs h
  weak_factorization_two := transferred_second_wfs (transferredAdjunction adj)
  complete := inferInstance
  cocomplete := inferInstance
  locallyPresentable := inferInstance
  leftProper := Boundaries.left_proper h
  rightProper := transferred_right_proper (transferredAdjunction adj)
  leftQuillen f hm := by
    let := hm
    exact ⟨left_preserves_cofibrations (transferredAdjunction adj) f,
      left_preserves_weak h f⟩
  quillenEquivalence K Y _ f := adjoint_weak_iff h K Y f

end Thomason.AbstractTransfer

end

end OAI
end


