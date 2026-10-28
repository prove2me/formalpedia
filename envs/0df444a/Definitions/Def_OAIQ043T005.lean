-- Prove2me | Definitions.Def_OAIQ043T005
-- name    : OAIQ043T005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:47:58.536596+00:00
-- url     : https://prove2.me/theorems/674b87ad-031e-4b76-8d95-8015bdcfe9f6
-- title:
--   Definitions bundle OAIQ043T005 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 224 declarations of OpenAI's Lean: 33 definitions, 3 inductive types or structures, 27 instances and 161 theorems. The definitions and types are `OAI.Thomason.Attachments.IsPosetAttachmentPiece`, `OAI.Thomason.Attachments.IsPosetNewPiece`, `OAI.Thomason.Attachments.maxFiniteLabel`, `OAI.Thomason.DirectedComplex.lambdaCounit`, `OAI.Thomason.DirectedComplex.verticalRow`, `OAI.Thomason.DirectedComplex.verticalTable`, `OAI.Thomason.FiniteVertexChain.Supports`, `OAI.Thomason.FiniteVertexChain.lift`, `OAI.Thomason.FiniteVertexChain.liftAt`, `OAI.Thomason.GlobeComplex.basis`, `OAI.Thomason.GlobeComplex.complex`, `OAI.Thomason.GlobeComplex.shiftDown`, `OAI.Thomason.GlobeComplex.topRow`, `OAI.Thomason.GlobeComplex.topTable`, `OAI.Thomason.NormalizedChains.AtomPasting`, `OAI.Thomason.NormalizedChains.SimplexAtomData`, `OAI.Thomason.NormalizedChains.SimplexAtomData.cone`, `OAI.Thomason.NormalizedChains.SimplexAtomData.singleton`, `OAI.Thomason.NormalizedChains.TopPasting`, `OAI.Thomason.NormalizedChains.atomCounitInverse`, `OAI.Thomason.NormalizedChains.basisLambda`, `OAI.Thomason.NormalizedChains.simplexAtom`, `OAI.Thomason.NormalizedChains.simplexCounitInverse`, `OAI.Thomason.OmegaCategory.FilteredColimit.globeHomIsColimit`, `OAI.Thomason.OmegaCategory.Functor.linearization`, `OAI.Thomason.OmegaCategory.lambdaUnit`, `OAI.Thomason.OmegaCategory.maxLabel`, `OAI.Thomason.lambdaNuBackward`, `OAI.Thomason.lambdaNuForward`, `OAI.Thomason.liftedBasis`, `OAI.Thomason.liftedChainMap`, `OAI.Thomason.orientalChain`, `OAI.Thomason.posetPieceFiberIso`, `OAI.Thomason.posetTableInverse`, `OAI.Thomason.posetTableInverseMap`, `OAI.Thomason.tableChainSupport`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_BoundaryQuotients`, `Thomason_Couniversality`, `Thomason_FilteredColimits`, `Thomason_FiniteAttachments`, `Thomason_FiniteChains`, `Thomason_Generators`, `Thomason_Globes`, `Thomason_GlobularComplexes`, `Thomason_GrayGenerators`, `Thomason_GreatestAttachments`, `Thomason_HornRealization`, `Thomason_LabelledFibers`, `Thomason_Linearization`, `Thomason_OrientalCounit`, `Thomason_Presentations`, `Thomason_RecursiveCylinders`, `Thomason_SieveAttachments`, `Thomason_SimplexAtoms`, `Thomason_SimplexColimits`, `Thomason_SimplexRanks`, `Thomason_SkeletalCategories`, `Thomason_SubdivisionFaces`, `Thomason_SubdivisionWeak`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T002` and `OAIQ043T003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T006` and `OAIQ043T007`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T002
import Definitions.Def_OAIQ043T003

section
-- module Solutions.OAIQ043_TH.Thomason_Presentations
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.hasLimits _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFaithfulNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFullNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.nCategoryInclusion_preservesLimits _root_.OAI.Thomason.OmegaCategory.nCategory_hasLimits _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.oneFiber_preservesColimits _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.opFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetFinite_preservesFilteredColimits _root_.OAI.Thomason.streetNerveFiniteOne_faithful _root_.OAI.Thomason.streetNerveFiniteOne_full _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Presentation

variable (P : Presentation.{u})


lemma generator_bounded (g : P.Generator) :
    P.category.source (P.dimension g) (P.generator g) = P.generator g := by
  apply P.cells_ext
  intro C I
  exact I.bounded g

end Thomason.OmegaCategory.Presentation

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


open CategoryTheory


noncomputable instance truncation_preservesColimits (n : ℕ) :
    Limits.PreservesColimitsOfSize.{v,w} (truncationFunctor.{u} n) :=
  (truncationAdjunction n).leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


noncomputable instance raisedOrientals_hasLeftKan :
    SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension raisedOrientals.{u} := by
  change (uliftYoneda.{u} : SimplexCategory ⥤ (SimplexCategoryᵒᵖ ⥤ Type u)).HasPointwiseLeftKanExtension raisedOrientals
  infer_instance


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

noncomputable instance nCategory_hasColimits (n : ℕ) : HasColimitsOfSize.{u,u} (NCategory.{u} n) :=
  hasColimits_of_reflective (nCategoryInclusion n)

end Thomason.OmegaCategory

end

end OAI
end

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

open NormalizedChains

lemma simplex_objects_mem_sieve {C : OmegaCategory.{u}} {m : ℕ}
    (F : Functor (Oriental m) C) {S : Set C.Objects} (hS : C.IsObjectSieve S)
    (hm : F.objects (tableObjectsEquiv.symm (Fin.last m)) ∈ S) :
    ∀ a : (Oriental m).Objects, F.objects a ∈ S := by
  intro a
  let i := tableObjectsEquiv a
  have h := hS (F.map (edgeTable i (Fin.last m) (Fin.le_last i)))
  have hs := (F.objects_source (edgeTable i (Fin.last m) (Fin.le_last i))).symm
  have ht := (F.objects_target (edgeTable i (Fin.last m) (Fin.le_last i))).symm
  have es : (Oriental m).sourceObject (edgeTable i (Fin.last m) (Fin.le_last i)) =
      tableObjectsEquiv.symm i := edgeTable_sourceObject _ _ _
  have et : (Oriental m).targetObject (edgeTable i (Fin.last m) (Fin.le_last i)) =
      tableObjectsEquiv.symm (Fin.last m) := edgeTable_targetObject _ _ _
  rw [es] at hs
  rw [et] at ht
  rw [hs, ht] at h
  have hi := h hm
  have he : tableObjectsEquiv.symm i = a :=
    (tableObjectsEquiv (E := Fin (m+1))).symm_apply_apply a
  exact he ▸ hi

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma lambdaUnitTable_source (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.lambdaUnitTable (C.source k x) =
      DirectedComplex.Table.truncate k false (C.lambdaUnitTable x) := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.truncate_row]
  by_cases hpk : p < k
  · simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [C.sourceCell_source_lt hpk]
    · rw [C.targetCell_source_lt hpk]
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_false, Bool.false_eq_true]
      have hs : C.sourceCell k (C.source k x) = C.sourceCell k x :=
        Subtype.ext (C.source_source_self k x)
      have ht : C.targetCell k (C.source k x) = C.sourceCell k x :=
        Subtype.ext (C.target_source_self k x)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, ht] <;> rfl
    · have hkp : k < p := by omega
      simp only [hpk, he]
      cases b <;> first
        | exact C.lambdaGen_source_above hkp x
        | exact C.lambdaGen_target_above hkp x

lemma lambdaUnitTable_target (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.lambdaUnitTable (C.target k x) =
      DirectedComplex.Table.truncate k true (C.lambdaUnitTable x) := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.truncate_row]
  by_cases hpk : p < k
  · simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [C.sourceCell_target_lt hpk]
    · rw [C.targetCell_target_lt hpk]
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_true]
      have hs : C.sourceCell k (C.target k x) = C.targetCell k x :=
        Subtype.ext (C.source_target_self k x)
      have ht : C.targetCell k (C.target k x) = C.targetCell k x :=
        Subtype.ext (C.target_target_self k x)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hs, ht] <;> rfl
    · have hkp : k < p := by omega
      simp only [hpk, he]
      have hk : C.source k (C.target k x) = C.target k x := C.source_target_self k x
      rw [← hk]
      cases b <;> first
        | exact C.lambdaGen_source_above hkp (C.target k x)
        | exact C.lambdaGen_target_above hkp (C.target k x)

lemma lambdaUnitTable_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y)
    (h' : DirectedComplex.Table.truncate k true (C.lambdaUnitTable x) =
      DirectedComplex.Table.truncate k false (C.lambdaUnitTable y)) :
    C.lambdaUnitTable (C.comp k x y h) =
      DirectedComplex.Table.comp k (C.lambdaUnitTable x) (C.lambdaUnitTable y) h' := by
  ext p b
  simp only [lambdaUnitTable_row, DirectedComplex.Table.comp_row]
  by_cases hpk : p < k
  · have he : C.target p y = C.target p x := by
      have hh := congrArg (C.target p) h
      simpa only [C.target_target, Nat.min_eq_left (le_of_lt hpk),
        C.target_source, ite_eq_left hpk] using hh.symm
    simp only [hpk]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · congr 1
      exact Subtype.ext (C.source_comp_le p k (le_of_lt hpk) x y h)
    · congr 1
      exact Subtype.ext ((C.target_comp_le p k (le_of_lt hpk) x y h).trans he)
  · by_cases he : p = k
    · subst p
      simp only [lt_self_iff_false, ite_true]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · congr 1
        exact Subtype.ext (C.source_comp_le k k le_rfl x y h)
      · congr 1
        exact Subtype.ext (C.target_comp_le k k le_rfl x y h)
    · have hkp : k < p := by omega
      simp only [hpk, he]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [C.sourceCell_comp_lt hkp]
        exact C.lambdaGen_comp hkp _ _ _
      · rw [C.targetCell_comp_lt hkp]
        exact C.lambdaGen_comp hkp _ _ _

def lambdaUnit (C : OmegaCategory.{u}) : Functor C C.linearization.nu where
  map := C.lambdaUnitTable
  map_source := C.lambdaUnitTable_source
  map_target := C.lambdaUnitTable_target
  map_comp := C.lambdaUnitTable_comp

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexAtoms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteTables _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {E : OmegaCategory.{w}}

lemma lambdaMap_d (F : Functor C D) (n : ℕ) :
    (F.lambdaMap n).comp (C.lambdaD n) = (D.lambdaD n).comp (F.lambdaMap (n+1)) := by
  apply C.lambda_linear_ext
  intro x
  change F.lambdaMap n (C.lambdaD n (C.lambdaGen x)) =
    D.lambdaD n (F.lambdaMap (n+1) (C.lambdaGen x))
  calc
    _ = F.lambdaMap n (C.lambdaGen (C.targetCell n x.val) -
        C.lambdaGen (C.sourceCell n x.val)) := congrArg (F.lambdaMap n) (C.lambdaD_gen n x)
    _ = F.lambdaMap n (C.lambdaGen (C.targetCell n x.val)) -
        F.lambdaMap n (C.lambdaGen (C.sourceCell n x.val)) := map_sub _ _ _
    _ = D.lambdaGen (F.onCells n (C.targetCell n x.val)) -
        D.lambdaGen (F.onCells n (C.sourceCell n x.val)) :=
      congrArg₂ (· - ·) (F.lambdaMap_gen n _) (F.lambdaMap_gen n _)
    _ = D.lambdaGen (D.targetCell n (F.map x.val)) -
        D.lambdaGen (D.sourceCell n (F.map x.val)) :=
      congrArg₂ (fun a b => D.lambdaGen a - D.lambdaGen b)
        (F.onCells_target n x.val) (F.onCells_source n x.val)
    _ = D.lambdaD n (D.lambdaGen (F.onCells (n+1) x)) :=
      (D.lambdaD_gen n (F.onCells (n+1) x)).symm
    _ = _ := congrArg (D.lambdaD n) (F.lambdaMap_gen (n+1) x).symm

lemma lambdaMap_aug (F : Functor C D) : D.lambdaAug.comp (F.lambdaMap 0) = C.lambdaAug := by
  apply C.lambda_linear_ext
  intro x
  change D.lambdaAug (F.lambdaMap 0 (C.lambdaGen x)) = C.lambdaAug (C.lambdaGen x)
  exact (congrArg D.lambdaAug (F.lambdaMap_gen 0 x)).trans
    ((D.lambdaAug_gen (F.onCells 0 x)).trans (C.lambdaAug_gen x).symm)

lemma lambdaMap_positive (F : Functor C D) (n : ℕ) (x : C.LambdaChain n)
    (hx : x ∈ C.lambdaPositive n) : F.lambdaMap n x ∈ D.lambdaPositive n := by
  change x ∈ (D.lambdaPositive n).comap (F.lambdaMap n).toAddMonoidHom
  apply AddSubmonoid.closure_le.mpr ?_ hx
  rintro z ⟨y, rfl⟩
  change F.lambdaMap n (C.lambdaGen y) ∈ D.lambdaPositive n
  rw [F.lambdaMap_gen]
  exact D.lambdaGen_positive _

def linearization (F : Functor C D) : DirectedComplex.Hom C.linearization D.linearization where
  map n := (F.lambdaMap n).toAddMonoidHom
  map_d n x := LinearMap.congr_fun (F.lambdaMap_d n) x
  map_augmentation x := LinearMap.congr_fun F.lambdaMap_aug x
  map_positive := F.lambdaMap_positive

lemma lambdaMap_comp (F : Functor C D) (G : Functor D E) (n : ℕ) :
    (F.comp G).lambdaMap n = (G.lambdaMap n).comp (F.lambdaMap n) := by
  apply C.lambda_linear_ext
  intro x
  simp only [LinearMap.comp_apply]
  erw [lambdaMap_gen, lambdaMap_gen, lambdaMap_gen]
  rfl

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma lambda_add_ext (C : OmegaCategory.{u}) {n : ℕ} {M : Type v} [AddCommGroup M]
    (f g : C.LambdaChain n →+ M)
    (h : ∀ x : C.Cells n, f (C.lambdaGen x) = g (C.lambdaGen x)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact C.lambda_linear_ext f.toIntLinearMap g.toIntLinearMap h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

namespace Table

lemma row_top_fixed {K : DirectedComplex.{u}} (x : Table K) {k : ℕ}
    (h : truncate k false x = x) : x.row k false = x.row k true := by
  have he := congrArg (fun t : Table K => t.row k true) h
  simpa only [truncate_row, lt_self_iff_false, ite_false, ite_true] using he

end Table

open OmegaCategory

lemma lambdaCounitMap_d (K : DirectedComplex.{u}) (n : ℕ) :
    (K.lambdaCounitMap n).toAddMonoidHom.comp (K.nu.lambdaD n).toAddMonoidHom =
      (K.d n).comp (K.lambdaCounitMap (n+1)).toAddMonoidHom := by
  apply K.nu.lambda_add_ext
  intro x
  change K.lambdaCounitMap n (K.nu.lambdaD n (K.nu.lambdaGen x)) =
    K.d n (K.lambdaCounitMap (n+1) (K.nu.lambdaGen x))
  erw [lambdaD_gen, map_sub, lambdaCounitMap_gen, lambdaCounitMap_gen, lambdaCounitMap_gen]
  change (Table.truncate n true x.val).row n false -
    (Table.truncate n false x.val).row n false = K.d n (x.val.row (n+1) false)
  erw [Table.truncate_row n true x.val n false, Table.truncate_row n false x.val n false]
  simp only [lt_self_iff_false, ite_false, ite_true]
  exact (x.val.boundary n false).symm

lemma lambdaCounitMap_aug (K : DirectedComplex.{u}) :
    K.augmentation.comp (K.lambdaCounitMap 0).toAddMonoidHom = K.nu.lambdaAug.toAddMonoidHom := by
  apply K.nu.lambda_add_ext
  intro x
  change K.augmentation (K.lambdaCounitMap 0 (K.nu.lambdaGen x)) = K.nu.lambdaAug (K.nu.lambdaGen x)
  erw [lambdaCounitMap_gen, lambdaAug_gen]
  exact x.val.augmentation false

lemma lambdaCounitMap_positive (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.LambdaChain n)
    (hx : x ∈ K.nu.lambdaPositive n) : K.lambdaCounitMap n x ∈ K.positive n := by
  change x ∈ (K.positive n).comap (K.lambdaCounitMap n).toAddMonoidHom
  apply AddSubmonoid.closure_le.mpr ?_ hx
  rintro z ⟨y, rfl⟩
  change K.lambdaCounitMap n (K.nu.lambdaGen y) ∈ K.positive n
  rw [K.lambdaCounitMap_gen]
  exact y.val.positive n false

def lambdaCounit (K : DirectedComplex.{u}) : Hom K.nu.linearization K where
  map n := (K.lambdaCounitMap n).toAddMonoidHom
  map_d n x := DFunLike.congr_fun (K.lambdaCounitMap_d n) x
  map_augmentation x := DFunLike.congr_fun K.lambdaCounitMap_aug x
  map_positive := K.lambdaCounitMap_positive

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason

def lambdaNuForward {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (f : DirectedComplex.Hom C.linearization K) : OmegaCategory.Functor C K.nu :=
  C.lambdaUnit.comp f.nu

def lambdaNuBackward {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) : DirectedComplex.Hom C.linearization K :=
  F.linearization.comp K.lambdaCounit

lemma lambdaNuBackward_gen {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) (n : ℕ) (x : C.Cells n) :
    (lambdaNuBackward F).map n (C.lambdaGen x) = (F.map x.val).row n false := by
  exact (congrArg (K.lambdaCounitMap n) (F.lambdaMap_gen n x)).trans
    (K.lambdaCounitMap_gen n (F.onCells n x))

lemma lambdaNu_left_inv {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (f : DirectedComplex.Hom C.linearization K) :
    lambdaNuBackward (lambdaNuForward f) = f := by
  apply DirectedComplex.Hom.ext
  funext n
  apply C.lambda_add_ext
  intro x
  calc
    _ = ((lambdaNuForward f).map x.val).row n false :=
      lambdaNuBackward_gen (lambdaNuForward f) n x
    _ = f.map n (C.lambdaGen (C.sourceCell n x.val)) := rfl
    _ = f.map n (C.lambdaGen x) :=
      congrArg (fun z => f.map n (C.lambdaGen z)) (Subtype.ext x.property)

lemma lambdaNu_right_inv {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) :
    lambdaNuForward (lambdaNuBackward F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  apply DirectedComplex.Table.ext
  funext p b
  cases b
  · change (lambdaNuBackward F).map p (C.lambdaGen (C.sourceCell p x)) = (F.map x).row p false
    calc
      _ = (F.map (C.source p x)).row p false := lambdaNuBackward_gen F p (C.sourceCell p x)
      _ = (DirectedComplex.Table.truncate p false (F.map x)).row p false :=
        congrArg (fun t : DirectedComplex.Table K => t.row p false) (F.map_source p x)
      _ = _ := DirectedComplex.Table.truncate_top_row p false (F.map x) false
  · change (lambdaNuBackward F).map p (C.lambdaGen (C.targetCell p x)) = (F.map x).row p true
    calc
      _ = (F.map (C.target p x)).row p false := lambdaNuBackward_gen F p (C.targetCell p x)
      _ = (DirectedComplex.Table.truncate p true (F.map x)).row p false :=
        congrArg (fun t : DirectedComplex.Table K => t.row p false) (F.map_target p x)
      _ = _ := DirectedComplex.Table.truncate_top_row p true (F.map x) false

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma coneTable_row_zero (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) (b : Bool) :
    (coneTable a x hx).row 0 b =
      if b then x.row 0 true else ⟨bracket [a], bracket_mem_grade [a]⟩ := rfl

lemma coneTable_row_succ (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) (p : ℕ) (b : Bool) :
    (coneTable a x hx).row (p+1) b =
      if b then x.row (p+1) true +
        ⟨prepend a (x.row p false).val, prepend_mem_grade a (x.row p false).property⟩
      else ⟨prepend a (x.row p true).val, prepend_mem_grade a (x.row p true).property⟩ := rfl

lemma coneTable_supported {S : Set E} {a : E} (ha : a ∈ S) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a))
    (hS : ∀ p b, (x.row p b).val ∈ supportedOn S) :
    ∀ p b, ((coneTable a x hx).row p b).val ∈ supportedOn S := by
  intro p b
  cases p with
  | zero =>
    cases b
    · exact bracket_mem_supportedOn (by simpa using ha)
    · exact hS 0 true
  | succ p =>
    cases b
    · exact prepend_mem_supportedOn ha (hS p true)
    · exact (supportedOn S).add_mem (hS (p+1) true) (prepend_mem_supportedOn ha (hS p false))

lemma coneTable_dimension (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) {k : ℕ}
    (hk : Table.truncate k false x = x) :
    Table.truncate (k+1) false (coneTable a x hx) = coneTable a x hx := by
  ext p b
  by_cases hp : p < k+1
  · simp only [Table.truncate_row, hp, ite_true]
  · by_cases he : p = k+1
    · subst p
      rw [Table.truncate_top_row]
      cases b
      · rfl
      · apply Subtype.ext
        change prepend a (x.row k true).val =
          (x.row (k+1) true).val + prepend a (x.row k false).val
        rw [Table.row_above_fixed x hk (by omega : k < k+1) true,
          Table.row_top_fixed x hk]
        exact (zero_add _).symm
    · rw [Table.truncate_row, ite_eq_right hp, ite_eq_right he]
      cases p with
      | zero => omega
      | succ p =>
        have hkp : k < p := by omega
        cases b <;> apply Subtype.ext
        · change 0 = prepend a (x.row p true).val
          rw [Table.row_above_fixed x hk hkp true]
          exact (map_zero _).symm
        · change 0 = (x.row (p+1) true).val + prepend a (x.row p false).val
          rw [Table.row_above_fixed x hk (by omega : k < p+1) true,
            Table.row_above_fixed x hk hkp false]
          exact ((zero_add _).trans (map_zero _)).symm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

structure SimplexAtomData (l : List E) where
  table : Table (complex E)
  supported : ∀ p b, (table.row p b).val ∈ supportedOn {a | a ∈ l}
  dimension : Table.truncate (l.length-1) false table = table
  top : ∀ b, (table.row (l.length-1) b).val = bracket l

namespace SimplexAtomData

def singleton (a : E) : SimplexAtomData [a] where
  table := vertexTable a
  supported p b := by
    cases p with
    | zero => exact bracket_mem_supportedOn (by simp)
    | succ p => exact (supportedOn _).zero_mem
  dimension := vertexTable_source a
  top _ := rfl

def cone (a : E) {l : List E} (hl : l ≠ []) (ha : ∀ b ∈ l, a ≤ b)
    (x : SimplexAtomData l) : SimplexAtomData (a :: l) := by
  have hx : ∀ p b, (x.table.row p b).val ∈ supportedOn (Set.Ici a) :=
    fun p b => supportedOn_mono ha (x.supported p b)
  have hlen : l.length - 1 + 1 = l.length := by
    have := List.length_pos_iff.mpr hl
    omega
  refine {
    table := coneTable a x.table hx
    supported := coneTable_supported (S := {b | b ∈ a :: l}) (by simp) x.table hx
      (fun p b => supportedOn_mono (fun _ h => List.mem_cons_of_mem a h) (x.supported p b))
    dimension := ?_
    top := ?_ }
  · simpa only [List.length_cons, Nat.add_sub_cancel, hlen] using
      coneTable_dimension a x.table hx x.dimension
  · intro b
    change ((coneTable a x.table hx).row l.length b).val = bracket (a :: l)
    rw [← hlen, coneTable_row_succ]
    have hz := Table.row_above_fixed x.table x.dimension
      (show l.length-1 < l.length-1+1 by omega) true
    cases b
    · change prepend a (x.table.row (l.length-1) true).val = bracket (a :: l)
      rw [x.top, prepend_bracket]
    · change (x.table.row (l.length-1+1) true).val +
        prepend a (x.table.row (l.length-1) false).val = bracket (a :: l)
      rw [hz, x.top, prepend_bracket]
      exact zero_add _

end SimplexAtomData

def simplexAtom : (a : E) → (l : List E) → (a :: l).Pairwise (· ≤ ·) →
    SimplexAtomData (a :: l)
  | a, [], _ => SimplexAtomData.singleton a
  | a, b :: l, h => SimplexAtomData.cone a (by simp)
      (List.pairwise_cons.mp h).1 (simplexAtom b l h.tail)

lemma basis_has_atom (w : Word E) (p : ℕ) (hw : w.val.length = p+1) :
    ∃ x : (complex E).nu.Cells p, (x.val.row p false).val = bracket w.val := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hw
  | cons a l =>
    let x := simplexAtom a l (hl.imp le_of_lt)
    change (a :: l).length = p+1 at hw
    have hlen : (a :: l).length-1 = p := by omega
    refine ⟨⟨x.table, ?_⟩, ?_⟩
    · change Table.truncate p false x.table = x.table
      rw [← hlen]
      exact x.dimension
    · change (x.table.row p false).val = bracket (a :: l)
      rw [← hlen]
      exact x.top false

lemma normalized_lambdaCounit_surjective (p : ℕ) :
    Function.Surjective ((complex E).lambdaCounitMap p) := by
  classical
  intro c
  have hc : c.val ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1} := c.property
  rw [Finsupp.supported_eq_span_single] at hc
  have hgen : ∀ (z : Chains E), z ∈ Submodule.span ℤ
      ((fun w : Word E => Finsupp.single w 1) '' {w | w.val.length = p+1}) →
      ∀ hz : z ∈ grade (p+1),
        (⟨z, hz⟩ : (complex E).Chain p) ∈ LinearMap.range ((complex E).lambdaCounitMap p) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rintro hg
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨x, hx⟩ := basis_has_atom w p hw
      refine ⟨(complex E).nu.lambdaGen x, ?_⟩
      rw [(complex E).lambdaCounitMap_gen]
      apply Subtype.ext
      exact hx.trans (bracket_of_pairwise w.property)
    | zero =>
      intro hg
      exact ⟨0, map_zero _⟩
    | add z y hz hy ihz ihy =>
      intro hg
      have hzg : z ∈ grade (p+1) := by
        change z ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      have hyg : y ∈ grade (p+1) := by
        change y ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      obtain ⟨v, hv⟩ := ihz hzg
      obtain ⟨w, hw⟩ := ihy hyg
      refine ⟨v+w, ?_⟩
      rw [map_add, hv, hw]
      rfl
    | smul r z hz ih =>
      intro hg
      have hzg : z ∈ grade (p+1) := by
        change z ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      obtain ⟨v, hv⟩ := ih hzg
      refine ⟨r • v, ?_⟩
      rw [map_smul, hv]
      rfl
  exact hgen c.val hc c.property

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexRanks
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteTables _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Ranks. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma wordBoundary_rank {N : ℕ} (w t : Word (Fin (N+1))) :
    (wordBoundary w.val t > 0 → wordBoundary w.val t = 1 ∧ simplexRank t.val < simplexRank w.val) ∧
    (wordBoundary w.val t < 0 → wordBoundary w.val t = -1 ∧ simplexRank w.val < simplexRank t.val) := by
  rcases w with ⟨w, hw⟩
  induction w generalizing t with
  | nil => simp [wordBoundary]
  | cons a l ih =>
    have htail : l.Pairwise (· < ·) := hw.tail
    by_cases he : l = t.val
    · have hz : prepend a (wordBoundary l) t = 0 := by
        apply prepend_apply_zero
        intro q hq
        have ha : a ∈ l := he.symm ▸ hq ▸ (List.mem_cons_self : a ∈ a :: q)
        exact (lt_irrefl a) ((List.pairwise_cons.mp hw).1 a ha)
      rw [wordBoundary_cons, Finsupp.sub_apply, hz, sub_zero, bracket_apply, ite_eq_left he]
      constructor
      · intro _; exact ⟨rfl, he ▸ simplexRank_tail_lt hw⟩
      · norm_num
    · rw [wordBoundary_cons, Finsupp.sub_apply, bracket_apply, ite_eq_right he, zero_sub]
      cases ht : t.val with
      | nil =>
        have hz : prepend a (wordBoundary l) t = 0 :=
          prepend_apply_zero a _ t (by intro q; simp [ht])
        simp [hz]
      | cons b q =>
        by_cases hab : a = b
        · subst b
          have hq : (a :: q).Pairwise (· < ·) := ht ▸ t.property
          let t' : Word (Fin (N+1)) := ⟨q, hq.tail⟩
          have het : t = ⟨a :: t'.val, hq⟩ := Subtype.ext ht
          simp only [het, prepend_apply_cons]
          obtain ⟨hp, hn⟩ := ih t' htail
          constructor
          · intro h
            obtain ⟨hc, hr⟩ := hn (neg_pos.mp h)
            refine ⟨by simpa using congrArg Neg.neg hc, ?_⟩
            change (3 : ℤ) ^ (N-a.val) - simplexRank q <
              (3 : ℤ) ^ (N-a.val) - simplexRank l
            exact sub_lt_sub_left hr _
          · intro h
            obtain ⟨hc, hr⟩ := hp (neg_neg_iff_pos.mp h)
            refine ⟨by simpa using congrArg Neg.neg hc, ?_⟩
            change (3 : ℤ) ^ (N-a.val) - simplexRank l <
              (3 : ℤ) ^ (N-a.val) - simplexRank q
            exact sub_lt_sub_left hr _
        · have hz : prepend a (wordBoundary l) t = 0 := by
            apply prepend_apply_zero
            intro s hs
            have := (List.cons.inj (hs.trans ht)).1
            exact hab this
          simp [hz]

lemma simplex_peel_positive {N : ℕ} {z x : Chains (Fin (N+1))}
    (hz : Positive z) (hx : Positive x) (hy : Positive (x + boundary z))
    (w : Word (Fin (N+1))) (hw : 0 < z w)
    (hmax : ∀ q ∈ z.support, simplexRank q.val ≤ simplexRank w.val) :
    Positive (x + wordBoundary w.val) := by
  classical
  intro t
  change 0 ≤ x t + wordBoundary w.val t
  by_cases ht : 0 ≤ wordBoundary w.val t
  · exact add_nonneg (hx t) ht
  · obtain ⟨hcoef, hrank⟩ := (wordBoundary_rank w t).2 (lt_of_not_ge ht)
    have hnonpos (q : Word (Fin (N+1))) (hq : q ∈ z.support) :
        wordBoundary q.val t ≤ 0 := by
      by_contra hn
      have hr := ((wordBoundary_rank q t).1 (lt_of_not_ge hn)).2
      exact (not_lt_of_ge (hmax q hq)) (hrank.trans hr)
    have hbd : boundary z t ≤ -z w := by
      rw [boundary_apply, Finsupp.sum]
      calc
        ∑ q ∈ z.support, z q * wordBoundary q.val t ≤
            ∑ q ∈ z.support, if q = w then -z w else 0 := by
          apply Finset.sum_le_sum
          intro q hq
          by_cases he : q = w
          · subst q; simp only [hcoef, mul_neg, mul_one]; exact le_rfl
          · rw [ite_eq_right he]
            exact mul_nonpos_of_nonneg_of_nonpos (hz q) (hnonpos q hq)
        _ = -z w := by simp [Finsupp.mem_support_iff, ne_of_gt hw]
    have hyt := hy t
    change 0 ≤ x t + boundary z t at hyt
    rw [hcoef]
    omega

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

lemma extendTop_source (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) :
    truncate n false (extendTop n x hx c hc hp) = x := by
  ext p b
  rw [truncate_row]
  by_cases h₀ : p < n
  · rw [ite_eq_left h₀, extendTop_row, extensionRow_other n x c p b (by omega) (by omega)]
  · rw [ite_eq_right h₀]
    by_cases h₁ : p = n
    · subst p
      rw [ite_eq_left rfl, extendTop_row, extensionRow_middle]
      cases b
      · simp
      · simpa using row_top_fixed x hx
    · rw [ite_eq_right h₁, row_above_fixed x hx (by omega) b]

lemma extendTop_dimension (n : ℕ) (x : Table K) (hx : truncate n false x = x)
    (c : K.Chain (n+1)) (hc : c ∈ K.positive (n+1))
    (hp : x.row n false + K.d n c ∈ K.positive n) :
    truncate (n+1) false (extendTop n x hx c hc hp) = extendTop n x hx c hc hp := by
  ext p b
  rw [truncate_row]
  by_cases h₀ : p < n+1
  · exact ite_eq_left h₀
  · rw [ite_eq_right h₀]
    by_cases h₁ : p = n+1
    · subst p; simp
    · rw [ite_eq_right h₁, extendTop_row, extensionRow_other n x c p b (by omega) h₁,
        row_above_fixed x hx (by omega) b]

lemma eq_extendTop (n : ℕ) (y : Table K) (hy : truncate (n+1) false y = y) :
    ∃ (hc : y.row (n+1) false ∈ K.positive (n+1))
      (hp : (truncate n false y).row n false + K.d n (y.row (n+1) false) ∈ K.positive n),
      extendTop n (truncate n false y) (by rw [truncate_truncate_same]; simp)
        (y.row (n+1) false) hc hp = y := by
  have he : (truncate n false y).row n false + K.d n (y.row (n+1) false) = y.row n true := by
    rw [truncate_top_row, y.boundary]; abel
  refine ⟨y.positive (n+1) false, he ▸ y.positive n true, ?_⟩
  ext p b
  rw [extendTop_row]
  by_cases h₀ : p = n
  · subst p; rw [extensionRow_middle, truncate_top_row]
    cases b
    · simp
    · simpa only [ite_true, truncate_top_row] using he
  · by_cases h₁ : p = n+1
    · subst p; rw [extensionRow_top]
      cases b
      · rfl
      · exact row_top_fixed y hy
    · rw [extensionRow_other n _ _ p b h₀ h₁, truncate_row]
      by_cases hp : p < n
      · exact ite_eq_left hp
      · rw [ite_eq_right hp, ite_eq_right h₀, row_above_fixed y hy (by omega) b]

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

lemma ext_source_top {n : ℕ} {x y : Table K}
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (hs : truncate n false x = truncate n false y)
    (ht : x.row (n+1) false = y.row (n+1) false) : x = y := by
  obtain ⟨hcx, hpx, ex⟩ := eq_extendTop n x hx
  obtain ⟨hcy, hpy, ey⟩ := eq_extendTop n y hy
  rw [← ex, ← ey]
  congr 1

lemma fixed_of_top_zero {n : ℕ} {x : Table K}
    (hx : truncate (n+1) false x = x) (ht : x.row (n+1) false = 0) :
    truncate n false x = x := by
  have hm : x.row n true = x.row n false := by
    have h := x.boundary n false
    rw [ht, map_zero] at h
    exact sub_eq_zero.mp h.symm
  ext p b
  rw [truncate_row]
  by_cases hp : p < n
  · exact ite_eq_left hp
  · rw [ite_eq_right hp]
    by_cases he : p = n
    · subst p; rw [ite_eq_left rfl]; cases b <;> simp [hm]
    · rw [ite_eq_right he]
      by_cases he' : p = n+1
      · subst p
        cases b
        · exact ht.symm
        · exact (row_top_fixed x hx).symm.trans ht |>.symm
      · exact (row_above_fixed x hx (by omega) b).symm

lemma comp_dimension {n k : ℕ} (hkn : k < n) {x y : Table K}
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (h : truncate k true x = truncate k false y) :
    truncate n false (comp k x y h) = comp k x y h := by
  have h' : truncate k true (truncate n false x) = truncate k false (truncate n false y) := by
    simpa only [hx, hy] using h
  rw [truncate_comp_gt n k hkn false x y h h']
  simp only [hx, hy]

lemma split_top {n : ℕ} (y : Table K) (hy : truncate (n+1) false y = y)
    (c d : K.Chain (n+1)) (hc : c ∈ K.positive (n+1)) (hd : d ∈ K.positive (n+1))
    (ht : c + d = y.row (n+1) false)
    (hp : y.row n false + K.d n c ∈ K.positive n) :
    ∃ a b : Table K, ∃ h : truncate n true a = truncate n false b,
      truncate (n+1) false a = a ∧ truncate (n+1) false b = b ∧
      a.row (n+1) false = c ∧ b.row (n+1) false = d ∧ comp n a b h = y := by
  let x := truncate n false y
  have hx : truncate n false x = x := by simp [x, truncate_truncate_same]
  have hp' : x.row n false + K.d n c ∈ K.positive n := by simpa [x] using hp
  let a := extendTop n x hx c hc hp'
  have ha := extendTop_dimension n x hx c hc hp'
  let m := truncate n true a
  have hm : truncate n false m = m := by simp [m, truncate_truncate]
  have hmrow : m.row n false = y.row n false + K.d n c := by
    simp [m, a, x]
  have hpd : m.row n false + K.d n d ∈ K.positive n := by
    rw [hmrow, add_assoc, ← map_add, ht, y.boundary]
    convert y.positive n true using 1; abel
  let b := extendTop n m hm d hd hpd
  have hb := extendTop_dimension n m hm d hd hpd
  have hab : truncate n true a = truncate n false b := (extendTop_source n m hm d hd hpd).symm
  refine ⟨a, b, hab, ha, hb, by simp [a], by simp [b], ?_⟩
  apply ext_source_top (comp_dimension (by omega : n < n+1) ha hb hab) hy
  · rw [source_comp_le n n le_rfl, extendTop_source]
  · simpa [a, b] using ht

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

inductive TopPasting (N n : ℕ) : Table (complex (Fin (N+1))) → Prop
  | identity (x) : truncate n false x = x → TopPasting N n x
  | basis (x : Table (complex (Fin (N+1)))) (w : Word (Fin (N+1))) : truncate (n+1) false x = x →
      (x.row (n+1) false).val = bracket w.val → TopPasting N n x
  | compose (x y) (h : truncate n true x = truncate n false y) :
      TopPasting N n x → TopPasting N n y → TopPasting N n (comp n x y h)

lemma oriental_top_pasting {N n : ℕ} (y : Table (complex (Fin (N+1))))
    (hy : truncate (n+1) false y = y) : TopPasting N n y := by
  classical
  generalize hm : (chainMass (y.row (n+1) false).val).toNat = m
  induction m using Nat.strong_induction_on generalizing y with
  | h m ih =>
    let z := (y.row (n+1) false).val
    have hz : Positive z := y.positive (n+1) false
    by_cases he : z = 0
    · exact .identity y (fixed_of_top_zero hy (Subtype.ext he))
    have hs : z.support.Nonempty := by
      by_contra hs
      exact he (Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs))
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image z.support (fun w => simplexRank w.val) hs
    have hwpos : 0 < z w := lt_of_le_of_ne (hz w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
    have hwlen : w.val.length = n+1+1 := by
      have := (mem_grade_iff (n+1+1) z).mp (y.row (n+1) false).property w
      exact this (Finsupp.mem_support_iff.mp hw)
    let c : (complex (Fin (N+1))).Chain (n+1) :=
      ⟨bracket w.val, hwlen ▸ bracket_mem_grade w.val⟩
    let d := y.row (n+1) false - c
    have hc : c ∈ (complex (Fin (N+1))).positive (n+1) := bracket_positive w.val
    have hd : d ∈ (complex (Fin (N+1))).positive (n+1) := simplex_peel_remainder hz w hwpos
    have ht : c + d = y.row (n+1) false := by dsimp [d]; abel
    have hx : Positive (y.row n false).val := y.positive n false
    have hfinal : Positive ((y.row n false).val + boundary z) := by
      have hb := congrArg Subtype.val (y.boundary n false)
      change boundary z = (y.row n true).val - (y.row n false).val at hb
      rw [hb]
      convert (show Positive (y.row n true).val from y.positive n true) using 1; abel
    have hp : y.row n false + (complex (Fin (N+1))).d n c ∈
        (complex (Fin (N+1))).positive n := by
      change Positive ((y.row n false).val + boundary (bracket w.val))
      rw [boundary_bracket (w.property.imp le_of_lt)]
      exact simplex_peel_positive hz hx hfinal w hwpos hmax
    obtain ⟨a, b, hab, ha, hb, hat, hbt, hyab⟩ := split_top y hy c d hc hd ht hp
    have hmass : (chainMass (b.row (n+1) false).val).toNat < m := by
      have he : (b.row (n+1) false).val = z - bracket w.val := congrArg Subtype.val hbt
      rw [he, map_sub, chainMass_bracket, ← hm]
      change (chainMass z - 1).toNat < (chainMass z).toNat
      rw [Int.toNat_lt_toNat (chainMass_pos hz hwpos)]
      omega
    rw [← hyab]
    exact .compose a b hab (.basis a w ha (congrArg Subtype.val hat))
      (ih _ hmass b hb rfl)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

lemma prepend_support {E : Type u} [PartialOrder E] (a : E) (c : Chains E) (w : Word E)
    (hw : prepend a c w ≠ 0) :
    ∃ q : Word E, w.val = a :: q.val ∧ c q ≠ 0 := by
  classical
  have he : ∃ q, w.val = a :: q := by
    by_contra h
    apply hw
    exact prepend_apply_zero a c w (fun q hq => h ⟨q, hq.symm⟩)
  obtain ⟨q, hq⟩ := he
  let t : Word E := ⟨q, (hq ▸ w.property).tail⟩
  refine ⟨t, hq, ?_⟩
  have ht : w = ⟨a :: t.val, hq ▸ w.property⟩ := Subtype.ext hq
  rw [ht, prepend_apply_cons] at hw
  exact hw

lemma simplexAtom_rank {N : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (h : (a :: l).Pairwise (· < ·)) (p : ℕ) (hp : p < l.length)
    (b : Bool) (w : Word (Fin (N+1)))
    (hw : (((simplexAtom a l (h.imp le_of_lt)).table.row p b).val) w ≠ 0) :
    if b then simplexRank w.val < simplexRank (a :: l)
    else simplexRank (a :: l) < simplexRank w.val := by
  classical
  induction l generalizing a p b w with
  | nil => simp at hp
  | cons c l ih =>
    let x := simplexAtom c l (h.tail.imp le_of_lt)
    have ha : ∀ d ∈ c :: l, a < d := (List.pairwise_cons.mp h).1
    have hx : ∀ p b, (x.table.row p b).val ∈ supportedOn (Set.Ici a) :=
      fun p b => supportedOn_mono (fun d hd => (ha d hd).le) (x.supported p b)
    have het : (simplexAtom a (c :: l) (h.imp le_of_lt)).table =
        coneTable a x.table hx := rfl
    rw [het] at hw
    cases p with
    | zero =>
      rw [coneTable_row_zero] at hw
      cases b
      · change bracket [a] w ≠ 0 at hw
        rw [bracket_apply] at hw
        have he : [a] = w.val := by split_ifs at hw with he; exact he; contradiction
        change simplexRank (a :: c :: l) < simplexRank w.val
        rw [← he]
        have hc := (simplexRank_bounds h.tail).1
        simp only [simplexRank]
        change (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l) <
          (3 : ℤ) ^ (N-a.val) - 0
        omega
      · change (x.table.row 0 true).val w ≠ 0 at hw
        have hs := (mem_supportedOn_iff {d | d ∈ c :: l} _).mp (x.supported 0 true) w hw
        exact simplexRank_of_after_lt h w (fun d hd => ha d (hs d hd))
    | succ p =>
      rw [coneTable_row_succ] at hw
      have hp' : p < l.length := by simpa using hp
      cases b
      · change prepend a (x.table.row p true).val w ≠ 0 at hw
        obtain ⟨q, hq, hc⟩ := prepend_support a _ w hw
        have hr := ih c h.tail p hp' true q hc
        change simplexRank (a :: c :: l) < simplexRank w.val
        rw [hq]
        change (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l) <
          (3 : ℤ) ^ (N-a.val) - simplexRank q.val
        exact sub_lt_sub_left hr _
      · change ((x.table.row (p+1) true).val + prepend a (x.table.row p false).val) w ≠ 0 at hw
        have he : (x.table.row (p+1) true).val w ≠ 0 ∨
            prepend a (x.table.row p false).val w ≠ 0 := by
          by_contra hn
          simp only [not_or, not_not] at hn
          exact hw (by simp only [Finsupp.add_apply, hn.1, hn.2, add_zero])
        rcases he with he | he
        · have hs := (mem_supportedOn_iff {d | d ∈ c :: l} _).mp
            (x.supported (p+1) true) w he
          exact simplexRank_of_after_lt h w (fun d hd => ha d (hs d hd))
        · obtain ⟨q, hq, hc⟩ := prepend_support a _ w he
          have hr := ih c h.tail p hp' false q hc
          change simplexRank w.val < simplexRank (a :: c :: l)
          rw [hq]
          change (3 : ℤ) ^ (N-a.val) - simplexRank q.val <
            (3 : ℤ) ^ (N-a.val) - simplexRank (c :: l)
          exact sub_lt_sub_left hr _

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_OrientalCounit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteTables _root_.OAI.Thomason.NormalizedChains.finiteWord _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oriental Counit. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

variable {K : DirectedComplex.{u}}

lemma factor_context (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (hc : c ∈ K.positive (k+1)) (hd : d ∈ K.positive (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) :
    ∃ (l r : Table K) (hlm : truncate k true l = truncate k false (removeContext k y c d ht hs he))
      (hmr : truncate k true (comp k l (removeContext k y c d ht hs he) hlm) = truncate k false r),
      truncate (k+1) false l = l ∧ truncate (k+1) false r = r ∧
      comp k (comp k l (removeContext k y c d ht hs he) hlm) r hmr = y := by
  let m := removeContext k y c d ht hs he
  let s := truncate k false y
  have hsf : truncate k false s = s := by simp [s, truncate_truncate_same]
  have hs' : s.row k false + K.d k c ∈ K.positive k := by simpa [s] using hs
  let l := extendTop k s hsf c hc hs'
  have hlm : truncate k true l = truncate k false m := by
    ext p b
    rw [truncate_row, truncate_row]
    by_cases hp : p < k
    · simp only [ite_eq_left hp]
      change extensionRow k s c p b = removeContextRow k y c d p b
      rw [extensionRow_other k s c p b (by omega) (by omega),
        removeContextRow_other k y c d p b (by omega) (by omega)]
      simp [s, hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases heq : p = k
      · subst p
        simp only [ite_true]
        change extensionRow k s c k true = removeContextRow k y c d k false
        simp [s]
      · simp only [ite_eq_right heq]
  let t := truncate k true m
  have htf : truncate k false t = t := by simp [t, truncate_truncate]
  have htrow : t.row k false = y.row k true - K.d k d := by simp [t, m]
  have ht' : t.row k false + K.d k d ∈ K.positive k := by
    rw [htrow, sub_add_cancel]; exact y.positive k true
  let r := extendTop k t htf d hd ht'
  have hmr : truncate k true (comp k l m hlm) = truncate k false r := by
    rw [target_comp_le k k le_rfl, extendTop_source]
  refine ⟨l, r, hlm, hmr, extendTop_dimension k s hsf c hc hs',
    extendTop_dimension k t htf d hd ht', ?_⟩
  ext p b
  simp only [comp_row]
  by_cases hp : p < k
  · simp only [ite_eq_left hp]
    change extensionRow k s c p b = y.row p b
    rw [extensionRow_other k s c p b (by omega) (by omega)]
    simp [s, hp]
  · simp only [ite_eq_right hp]
    by_cases heq : p = k
    · subst p
      simp only [ite_true]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        change extensionRow k s c k false = y.row k false
        simp [s]
      · simp only [ite_true]
        change extensionRow k t d k true = y.row k true
        simp only [extensionRow_middle, ite_true, htrow, sub_add_cancel]
    · simp only [ite_eq_right heq]
      by_cases hk : p = k+1
      · subst p
        change extensionRow k s c (k+1) b + removeContextRow k y c d (k+1) b +
          extensionRow k t d (k+1) b = y.row (k+1) b
        rw [extensionRow_top, extensionRow_top, removeContextRow_top]
        abel
      · change extensionRow k s c p b + removeContextRow k y c d p b +
          extensionRow k t d p b = y.row p b
        rw [extensionRow_other k s c p b heq hk, extensionRow_other k t d p b heq hk,
          removeContextRow_other k y c d p b heq hk]
        have hz₁ : s.row p b = 0 := by simp [s, hp, heq]
        have hz₂ : t.row p b = 0 := by simp [t, hp, heq]
        rw [hz₁, hz₂, zero_add, add_zero]

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma boundary_nonneg_of_before {N : ℕ} {z : Chains (Fin (N+1))} (hz : Positive z)
    (r : ℤ) (hs : ∀ w, z w ≠ 0 → r < simplexRank w.val)
    (t : Word (Fin (N+1))) (ht : simplexRank t.val ≤ r) : 0 ≤ boundary z t := by
  classical
  rw [boundary_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro w hw
  apply mul_nonneg (hz w)
  by_contra hn
  have hr := ((wordBoundary_rank w t).2 (lt_of_not_ge hn)).2
  have hh := hs w (Finsupp.mem_support_iff.mp hw)
  omega

lemma boundary_nonpos_of_after {N : ℕ} {z : Chains (Fin (N+1))} (hz : Positive z)
    (r : ℤ) (hs : ∀ w, z w ≠ 0 → simplexRank w.val ≤ r)
    (t : Word (Fin (N+1))) (ht : r ≤ simplexRank t.val) : boundary z t ≤ 0 := by
  classical
  rw [boundary_apply, Finsupp.sum]
  apply Finset.sum_nonpos
  intro w hw
  apply mul_nonpos_of_nonneg_of_nonpos (hz w)
  by_contra hn
  have hr := ((wordBoundary_rank w t).1 (lt_of_not_ge hn)).2
  have hh := hs w (Finsupp.mem_support_iff.mp hw)
  omega

lemma rankBefore_boundary_nonneg {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (r : ℤ) (t : Word (Fin (N+1))) (ht : simplexRank t.val ≤ r) :
    0 ≤ boundary (rankBefore z r) t := by
  apply boundary_nonneg_of_before (filter_positive z hz _) r _ t ht
  intro w hw
  by_contra hn
  exact hw (by simp [hn])

lemma rankAfter_boundary_nonpos {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (r : ℤ) (t : Word (Fin (N+1))) (ht : r ≤ simplexRank t.val) :
    boundary (rankAfter z r) t ≤ 0 := by
  apply boundary_nonpos_of_after (filter_positive z hz _) r _ t ht
  intro w hw
  by_contra hn
  exact hw (by simp [lt_of_not_ge hn])

lemma rank_cut_positive {N : ℕ} {a b x y z : Chains (Fin (N+1))} (r : ℤ)
    (ha : Positive a) (hb : Positive b) (hx : Positive x) (hy : Positive y) (hz : Positive z)
    (has : ∀ w, a w ≠ 0 → r < simplexRank w.val)
    (hbs : ∀ w, b w ≠ 0 → simplexRank w.val < r)
    (he : y - x = b - a + boundary z) :
    Positive (x + boundary (rankBefore z r)) ∧
      Positive (y - boundary (rankAfter z r)) := by
  have hh (t : Word (Fin (N+1))) :
      y t - x t = b t - a t + boundary (rankBefore z r) t + boundary (rankAfter z r) t := by
    have h := congrArg (fun z : Chains (Fin (N+1)) => z t) he
    rw [← rankBefore_add_rankAfter z r, map_add] at h
    simp only [Finsupp.sub_apply, Finsupp.add_apply] at h
    linarith
  constructor
  · intro t
    change 0 ≤ x t + boundary (rankBefore z r) t
    by_cases ht : simplexRank t.val ≤ r
    · exact add_nonneg (hx t) (rankBefore_boundary_nonneg hz r t ht)
    · have ht' : r < simplexRank t.val := lt_of_not_ge ht
      have hb₀ : b t = 0 := by
        by_contra hn
        have := hbs t hn
        omega
      have hlow := rankAfter_boundary_nonpos hz r t ht'.le
      have heq := hh t
      have hp := hy t
      have hn := ha t
      rw [hb₀] at heq
      omega
  · intro t
    change 0 ≤ y t - boundary (rankAfter z r) t
    by_cases ht : r ≤ simplexRank t.val
    · exact sub_nonneg.mpr (le_trans (rankAfter_boundary_nonpos hz r t ht) (hy t))
    · have ht' : simplexRank t.val < r := lt_of_not_ge ht
      have ha₀ : a t = 0 := by
        by_contra hn
        have := has t hn
        omega
      have hhigh := rankBefore_boundary_nonneg hz r t ht'.le
      have heq := hh t
      have hp := hx t
      have hn := hb t
      rw [ha₀] at heq
      omega

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

inductive AtomPasting (N : ℕ) : Table (complex (Fin (N+1))) → Prop
  | atom (a : Fin (N+1)) (l : List (Fin (N+1))) (h : (a :: l).Pairwise (· < ·)) :
      AtomPasting N (simplexAtom a l (h.imp le_of_lt)).table
  | compose (k : ℕ) (x y) (h : truncate k true x = truncate k false y) :
      AtomPasting N x → AtomPasting N y → AtomPasting N (comp k x y h)

lemma common_atom_context {N : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·)) (s : ℕ) (hs : s < l.length)
    (y : Table (complex (Fin (N+1))))
    (hy : y.row (s+1) false = (simplexAtom a l (ha.imp le_of_lt)).table.row (s+1) false) :
    Positive (y.row s false - (simplexAtom a l (ha.imp le_of_lt)).table.row s false).val ∧
      y.row s true - (simplexAtom a l (ha.imp le_of_lt)).table.row s true =
        y.row s false - (simplexAtom a l (ha.imp le_of_lt)).table.row s false := by
  let A := (simplexAtom a l (ha.imp le_of_lt)).table
  have he : y.row s true - y.row s false = A.row s true - A.row s false := by
    rw [← y.boundary s false, hy, A.boundary]
  have hraw := congrArg Subtype.val he
  change (y.row s true).val - (y.row s false).val =
    (A.row s true).val - (A.row s false).val at hraw
  obtain ⟨hz, hcommon⟩ := positive_common_context (y.positive s false) (y.positive s true)
    (fun w hw => by
      by_contra hn
      have hr₁ := simplexAtom_rank a l ha s hs false w hw
      have hr₂ := simplexAtom_rank a l ha s hs true w hn
      simp only [Bool.false_eq_true, ite_false, ite_true] at hr₁ hr₂
      omega) hraw
  exact ⟨hz, Subtype.ext hcommon⟩

lemma atom_context_pasting {N n : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·)) (hlen : l.length = n+1)
    (hsmall : ∀ x : Table (complex (Fin (N+1))), truncate n false x = x → AtomPasting N x)
    (k : ℕ) (hk : k ≤ n) (y : Table (complex (Fin (N+1))))
    (hy : ∀ p, k < p → ∀ b,
      y.row p b = (simplexAtom a l (ha.imp le_of_lt)).table.row p b) : AtomPasting N y := by
  let A := (simplexAtom a l (ha.imp le_of_lt)).table
  let r := simplexRank (a :: l)
  induction k generalizing y with
  | zero =>
    have hs : 0 < l.length := by omega
    obtain ⟨hz, hcommon⟩ := common_atom_context a l ha 0 hs y (hy 1 (by omega) false)
    let z := y.row 0 false - A.row 0 false
    have haug : (complex (Fin (N+1))).augmentation z = 0 := by
      dsimp [z]
      rw [map_sub, y.augmentation, A.augmentation, sub_self]
    have hz₀ : z = 0 := Subtype.ext
      (positive_augmentation_zero z.property hz haug)
    have heq : y = A := by
      ext p b
      cases p with
      | zero =>
        cases b
        · exact sub_eq_zero.mp hz₀
        · exact sub_eq_zero.mp (hcommon.trans hz₀)
      | succ p => exact hy (p+1) (by omega) b
    rw [heq]
    exact .atom a l ha
  | succ k ih =>
    have hs : k+1 < l.length := by omega
    obtain ⟨hz, hcommon⟩ := common_atom_context a l ha (k+1) hs y
      (hy (k+1+1) (by omega) false)
    let z := y.row (k+1) false - A.row (k+1) false
    let c : (complex (Fin (N+1))).Chain (k+1) :=
      ⟨rankBefore z.val r, filter_mem_grade z.val z.property _⟩
    let d : (complex (Fin (N+1))).Chain (k+1) :=
      ⟨rankAfter z.val r, filter_mem_grade z.val z.property _⟩
    have hc : c ∈ (complex (Fin (N+1))).positive (k+1) := filter_positive z.val hz _
    have hd : d ∈ (complex (Fin (N+1))).positive (k+1) := filter_positive z.val hz _
    have hcd : c + d = z := Subtype.ext (rankBefore_add_rankAfter z.val r)
    have hrows (b : Bool) : y.row (k+1) b - c - d = A.row (k+1) b := by
      have hz' : y.row (k+1) b - A.row (k+1) b = z := by
        cases b
        · rfl
        · exact hcommon
      rw [sub_sub, hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hz').trans (add_comm _ _))
    have ht : ∀ b, y.row (k+1) b - c - d ∈ (complex (Fin (N+1))).positive (k+1) := by
      intro b
      rw [hrows b]
      exact A.positive (k+1) b
    have hdiff : y.row k true - y.row k false = A.row k true - A.row k false +
        (complex (Fin (N+1))).d k z := by
      dsimp [z]
      rw [map_sub, y.boundary, A.boundary]
      abel
    have hraw := congrArg Subtype.val hdiff
    change (y.row k true).val - (y.row k false).val =
      (A.row k true).val - (A.row k false).val + boundary z.val at hraw
    obtain ⟨hstart, hend⟩ := rank_cut_positive r (A.positive k false) (A.positive k true)
      (y.positive k false) (y.positive k true) hz
      (fun w hw => simplexAtom_rank a l ha k (by omega) false w hw)
      (fun w hw => simplexAtom_rank a l ha k (by omega) true w hw) hraw
    have hstart' : y.row k false + (complex (Fin (N+1))).d k c ∈
        (complex (Fin (N+1))).positive k := hstart
    have hend' : y.row k true - (complex (Fin (N+1))).d k d ∈
        (complex (Fin (N+1))).positive k := hend
    let m := removeContext k y c d ht hstart' hend'
    have hm : AtomPasting N m := by
      apply ih (by omega) m
      intro p hp b
      change removeContextRow k y c d p b = A.row p b
      by_cases hpk : p = k+1
      · subst p
        rw [removeContextRow_top, hrows]
      · rw [removeContextRow_other k y c d p b (by omega) hpk]
        exact hy p (by omega) b
    obtain ⟨left, right, hlm, hmr, hl, hr, he⟩ := factor_context k y c d hc hd ht hstart' hend'
    rw [← he]
    exact .compose k _ _ hmr
      (.compose k _ _ hlm
        (hsmall left ((complex (Fin (N+1))).nu.source_fixed_upwards hk hl)) hm)
      (hsmall right ((complex (Fin (N+1))).nu.source_fixed_upwards hk hr))

lemma rows_above_top_agree {K : DirectedComplex.{u}} {n : ℕ} (x y : Table K)
    (hx : truncate n false x = x) (hy : truncate n false y = y)
    (ht : x.row n false = y.row n false) (p : ℕ) (hp : n ≤ p) (b : Bool) :
    x.row p b = y.row p b := by
  by_cases he : p = n
  · subst p
    cases b
    · exact ht
    · rw [← row_top_fixed x hx, ← row_top_fixed y hy, ht]
  · rw [row_above_fixed x hx (by omega) b, row_above_fixed y hy (by omega) b]

lemma oriental_atomic_pasting {N : ℕ} (n : ℕ) (y : Table (complex (Fin (N+1))))
    (hy : truncate n false y = y) : AtomPasting N y := by
  induction n generalizing y with
  | zero =>
    let x : (complex (Fin (N+1))).nu.Objects := ⟨y, hy⟩
    let a := tableObjectsEquiv x
    have he : vertexTable a = y := congrArg Subtype.val (tableObjectsEquiv.left_inv x)
    rw [← he]
    exact .atom a [] (by simp)
  | succ n ih =>
    have ht := oriental_top_pasting y hy
    clear hy
    induction ht with
    | identity x hx => exact ih x hx
    | basis x w hx hxt =>
      have hw : w.val.length = n+1+1 := by
        apply (mem_grade_iff (n+1+1) (x.row (n+1) false).val).mp
          (x.row (n+1) false).property w
        rw [hxt, bracket_of_pairwise w.property, Finsupp.single_eq_same]
        norm_num
      rcases w with ⟨w, hwp⟩
      cases w with
      | nil => simp at hw
      | cons a l =>
        have hlen : l.length = n+1 := by simpa using hw
        let A := simplexAtom a l (hwp.imp le_of_lt)
        have hdim : truncate (n+1) false A.table = A.table := by
          convert A.dimension using 1; simp [hlen]
        have htop : x.row (n+1) false = A.table.row (n+1) false := by
          apply Subtype.ext
          rw [hxt]
          have hh := A.top false
          have hidx : (a :: l).length - 1 = n+1 := by simpa using hlen
          rw [hidx] at hh
          exact hh.symm
        apply atom_context_pasting a l hwp hlen ih n le_rfl x
        intro p hp b
        exact rows_above_top_agree x A.table hx hdim htop p (by omega) b
    | compose x y h hx hy ihx ihy => exact .compose n x y h ihx ihy

lemma oriental_all_atomic {N : ℕ} (y : Table (complex (Fin (N+1)))) : AtomPasting N y := by
  obtain ⟨n, hn⟩ := (complex (Fin (N+1))).nu.finite_dimension y
  exact oriental_atomic_pasting n y hn

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table

lemma dimension_of_rows_above_zero {K : DirectedComplex.{u}} {n : ℕ} (x : Table K)
    (h : ∀ p, n < p → ∀ b, x.row p b = 0) : truncate n false x = x := by
  have ht : x.row n false = x.row n true := by
    have hz := x.boundary n false
    rw [h (n+1) (by omega) false, map_zero] at hz
    exact (sub_eq_zero.mp hz.symm).symm
  ext p b
  rw [truncate_row]
  by_cases hp : p < n
  · simp only [hp, ite_true]
  · by_cases he : p = n
    · subst p
      cases b <;> simp [ht]
    · simp only [hp, ite_false, he]
      exact (h p (by omega) b).symm

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

variable {E : Type u} [PartialOrder E]

lemma comp_dimension_factors {k n : ℕ} (x y : Table (complex E))
    (h : truncate k true x = truncate k false y)
    (hz : truncate n false (comp k x y h) = comp k x y h) :
    truncate n false x = x ∧ truncate n false y = y := by
  have habove (p : ℕ) (hp : max n k < p) (b : Bool) :
      x.row p b = 0 ∧ y.row p b = 0 := by
    have he := row_above_fixed (comp k x y h) hz (by omega : n < p) b
    rw [comp_row] at he
    simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false] at he
    have heraw := congrArg Subtype.val he
    change (x.row p b).val + (y.row p b).val = 0 at heraw
    obtain ⟨hx, hy⟩ := positive_add_zero (x.positive p b) (y.positive p b) heraw
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hx := dimension_of_rows_above_zero x (fun p hp b => (habove p hp b).1)
  have hy := dimension_of_rows_above_zero y (fun p hp b => (habove p hp b).2)
  by_cases hkn : k ≤ n
  · simpa only [max_eq_left hkn] using And.intro hx hy
  · have hnk : n ≤ k := by omega
    rw [max_eq_right hnk] at hx hy
    have hz' : truncate k false (comp k x y h) = comp k x y h :=
      (complex E).nu.source_fixed_upwards hnk hz
    have hz'' : truncate k true (comp k x y h) = comp k x y h :=
      (complex E).nu.target_eq_self_of_source_eq_self hz'
    have hzx : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx]
    have hzy : comp k x y h = y := by
      rw [← hz'', target_comp_le k k le_rfl]
      exact (complex E).nu.target_eq_self_of_source_eq_self hy
    exact ⟨hzx ▸ hz, hzy ▸ hz⟩

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table OmegaCategory

variable {E : Type u} [PartialOrder E]

noncomputable def basisLambda (p : ℕ) (w : Word E) : (complex E).nu.LambdaChain p := by
  classical
  by_cases h : w.val.length = p+1
  · rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      let A := simplexAtom a l (hw.imp le_of_lt)
      have he : (a :: l).length-1 = p := by simp only [List.length_cons] at h ⊢; omega
      exact (complex E).nu.lambdaGen ⟨A.table, he ▸ A.dimension⟩
  · exact 0

lemma basisLambda_cons (p : ℕ) (a : E) (l : List E) (ha : (a :: l).Pairwise (· < ·))
    (h : l.length = p)
    (hd : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) :
    basisLambda p ⟨a :: l, ha⟩ = (complex E).nu.lambdaGen ⟨_, hd⟩ := by
  simp [basisLambda, h]

noncomputable def atomCounitInverse (p : ℕ) :
    (complex E).Chain p →ₗ[ℤ] (complex E).nu.LambdaChain p :=
  (Finsupp.linearCombination ℤ (basisLambda p)).comp (grade (p+1)).subtype

lemma atomCounitInverse_bracket (p : ℕ) (w : Word E)
    (h : w.val.length = p+1) :
    atomCounitInverse p ⟨bracket w.val, h ▸ bracket_mem_grade w.val⟩ = basisLambda p w := by
  change Finsupp.linearCombination ℤ (basisLambda p) (bracket w.val) = _
  rw [bracket_of_pairwise w.property, Finsupp.linearCombination_single, one_smul]

lemma simplexAtom_dimension_le {N p : ℕ} (a : Fin (N+1)) (l : List (Fin (N+1)))
    (ha : (a :: l).Pairwise (· < ·))
    (h : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) : l.length ≤ p := by
  by_contra hn
  have hz := row_above_fixed (simplexAtom a l (ha.imp le_of_lt)).table h
    (lt_of_not_ge hn) false
  have ht := (simplexAtom a l (ha.imp le_of_lt)).top false
  change ((simplexAtom a l (ha.imp le_of_lt)).table.row l.length false).val =
    bracket (a :: l) at ht
  rw [hz] at ht
  change 0 = bracket (a :: l) at ht
  rw [bracket_of_pairwise ha] at ht
  have he := congrArg (fun z : Chains (Fin (N+1)) => z ⟨a :: l, ha⟩) ht
  simp at he

lemma atomCounitInverse_top {N p : ℕ} (y : Table (complex (Fin (N+1))))
    (hy : truncate p false y = y) :
    atomCounitInverse p (y.row p false) = (complex (Fin (N+1))).nu.lambdaGen ⟨y, hy⟩ := by
  revert hy
  induction oriental_all_atomic y with
  | atom a l ha =>
    intro hy
    let A := simplexAtom a l (ha.imp le_of_lt)
    have hp : l.length ≤ p := simplexAtom_dimension_le a l ha hy
    by_cases he : l.length = p
    · have hr : A.table.row p false =
          (⟨bracket (a :: l), (show (a :: l).length = p+1 by simp [he]) ▸
            bracket_mem_grade (a :: l)⟩ : (complex (Fin (N+1))).Chain p) := by
        apply Subtype.ext
        have ht := A.top false
        have hd : (a :: l).length-1 = p := by simp [he]
        rwa [hd] at ht
      change atomCounitInverse p (A.table.row p false) = _
      rw [hr, atomCounitInverse_bracket p ⟨a :: l, ha⟩ (by simp [he])]
      exact basisLambda_cons p a l ha he hy
    · have hlt : l.length < p := by omega
      have hd : truncate l.length false A.table = A.table := by
        simpa only [List.length_cons, Nat.add_sub_cancel] using A.dimension
      rw [row_above_fixed A.table hd hlt false, map_zero]
      exact ((complex (Fin (N+1))).nu.lambdaGen_degenerate hlt ⟨A.table, hy⟩ hd).symm
  | compose k x y h hx hy ihx ihy =>
    intro hz
    obtain ⟨hxd, hyd⟩ := comp_dimension_factors x y h hz
    by_cases hkp : k < p
    · have hgraded : (⟨comp k x y h, hz⟩ : (complex (Fin (N+1))).nu.Cells p) =
          (complex (Fin (N+1))).nu.gradedComp hkp ⟨x, hxd⟩ ⟨y, hyd⟩ h := rfl
      rw [hgraded]
      erw [(complex (Fin (N+1))).nu.lambdaGen_comp hkp]
      rw [comp_row]
      simp only [show ¬p < k by omega, show p ≠ k by omega, ite_false]
      rw [map_add, ihx hxd, ihy hyd]
    · have hpk : p ≤ k := by omega
      have hz' : truncate k false (comp k x y h) = comp k x y h :=
        (complex (Fin (N+1))).nu.source_fixed_upwards hpk hz
      have hx' : truncate k false x = x :=
        (complex (Fin (N+1))).nu.source_fixed_upwards hpk hxd
      have he : comp k x y h = x := by rw [← hz', source_comp_le k k le_rfl, hx']
      have hecell : (⟨comp k x y h, hz⟩ : (complex (Fin (N+1))).nu.Cells p) =
          ⟨x, hxd⟩ := Subtype.ext he
      rw [hecell, he]
      exact ihx hxd

lemma oriental_lambdaCounit_leftInverse {N : ℕ} (p : ℕ) :
    (atomCounitInverse p).comp ((complex (Fin (N+1))).lambdaCounitMap p) =
      LinearMap.id := by
  apply (complex (Fin (N+1))).nu.lambda_linear_ext
  intro x
  change atomCounitInverse p ((complex (Fin (N+1))).lambdaCounitMap p
    ((complex (Fin (N+1))).nu.lambdaGen x)) = (complex (Fin (N+1))).nu.lambdaGen x
  rw [(complex (Fin (N+1))).lambdaCounitMap_gen]
  exact atomCounitInverse_top x.val x.property

lemma oriental_lambdaCounit_injective {N : ℕ} (p : ℕ) :
    Function.Injective ((complex (Fin (N+1))).lambdaCounitMap p) := by
  apply Function.HasLeftInverse.injective
  refine ⟨atomCounitInverse p, ?_⟩
  intro x
  exact LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) x

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FilteredColimits
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable {K : DirectedComplex.{u}}

def verticalRow (x : Table K) : (p : ℕ) → Bool → K.cylinder.Chain p
  | 0, b => if b then (0, x.row 0 b) else (x.row 0 b, 0)
  | p+1, b => if Even (p+1) then
      (if b then (0, x.row (p+1) b, x.row p b)
        else (x.row (p+1) b, 0, x.row p b))
    else (if b then (x.row (p+1) b, 0, x.row p b)
        else (0, x.row (p+1) b, x.row p b))

lemma verticalRow_boundary (x : Table K) (p : ℕ) (b : Bool) :
    K.cylinder.d p (verticalRow x (p+1) b) =
      verticalRow x p true - verticalRow x p false := by
  cases p with
  | zero =>
    cases b <;> simp [verticalRow, cylinder, cylinderDifferential, x.boundary]
  | succ p =>
    by_cases hp : Even (p+1)
    · have hp' : ¬Even (p+1+1) := by rw [Nat.even_add_one]; exact not_not_intro hp
      have hs : (-1 : ℤ)^(p+1) = 1 := hp.neg_one_pow
      cases b <;>
        simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
    · have hp' : Even (p+1+1) := by rw [Nat.even_add_one]; exact hp
      have hs : (-1 : ℤ)^(p+1) = -1 := (Nat.not_even_iff_odd.mp hp).neg_one_pow
      cases b
      · simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
      · simp [verticalRow, hp, hp', cylinder, cylinderDifferential, hs, x.boundary]
        abel

def verticalTable (x : Table K) : Table K.cylinder where
  row := verticalRow x
  positive p b := by
    cases p with
    | zero => cases b <;> exact ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem,
        by first | exact x.positive _ _ | exact (K.positive _).zero_mem⟩
    | succ p =>
      dsimp only [verticalRow]
      split <;> cases b <;> exact ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem,
        ⟨by first | exact x.positive _ _ | exact (K.positive _).zero_mem, x.positive _ _⟩⟩
  boundary := verticalRow_boundary x
  augmentation b := by
    cases b <;> simp [verticalRow, cylinder, x.augmentation]
  bounded := by
    obtain ⟨n, hn⟩ := x.bounded
    refine ⟨n+1, ?_⟩
    intro p hp b
    cases p with
    | zero => omega
    | succ p =>
      have hnp : n < p := by omega
      have hnp' : n < p+1 := by omega
      simp [verticalRow, hn p hnp, hn (p+1) hnp']

lemma verticalTable_natural {L : DirectedComplex.{v}} (f : Hom K L) (x : Table K) :
    f.cylinder.nu.map (verticalTable x) = verticalTable (f.nu.map x) := by
  change f.cylinder.table (verticalTable x) = verticalTable (f.table x)
  ext p b
  cases p with
  | zero => cases b <;> simp [verticalTable, verticalRow, Hom.table,
      Hom.cylinder, Hom.cylinderMap]
  | succ p =>
    by_cases hp : Even (p+1) <;> cases b <;>
      simp [verticalTable, verticalRow, hp, Hom.table,
        Hom.cylinder, Hom.cylinderMap]

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason

instance orientalFiniteCells (m : ℕ) : Finite (Oriental m).Cell :=
  NormalizedChains.finiteTables

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Globes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFaithfulNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFullNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetFinite_preservesFilteredColimits _root_.OAI.Thomason.streetNerveFiniteOne_faithful _root_.OAI.Thomason.streetNerveFiniteOne_full _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

lemma globeGenerator_bounded (n : ℕ) :
    (globe.{u} n).source n (globeGenerator n) = globeGenerator n :=
  (globePresentation n).generator_bounded PUnit.unit

lemma globe_functor_ext {n : ℕ} {C : OmegaCategory.{u}} {F G : Functor (globe.{u} n) C}
    (h : F.map (globeGenerator n) = G.map (globeGenerator n)) : F = G := by
  apply (globePresentation n).functor_ext
  intro g
  cases g
  exact h

lemma globe_map_bounded {n : ℕ} {C : OmegaCategory.{u}} (F : Functor (globe.{u} n) C) :
    C.source n (F.map (globeGenerator n)) = F.map (globeGenerator n) := by
  rw [← F.map_source, globeGenerator_bounded]

namespace FilteredColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ OmegaCategory.{u})

lemma globe_functor_lift (n : ℕ) (G : Functor (globe.{u} n) (omega F)) :
    ∃ (i : J) (H : Functor (globe.{u} n) (F.obj i)),
      Functor.comp H ((cocone F).ι.app i) = G := by
  obtain ⟨i, x, hx⟩ := exists_rep F (G.map (globeGenerator n))
  have hb : ι F i ((F.obj i).source n x) = ι F i x := by
    rw [← source_ι, hx]
    exact globe_map_bounded G
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (CellDiagram F)) _ _).mp hb
  have hy : (F.obj j).source n ((F.map f).map x) = (F.map f).map x := by
    rw [← (F.map f).map_source]
    exact hf
  refine ⟨j, globeLift n _ hy, ?_⟩
  apply globe_functor_ext
  change ι F j ((F.map f).map x) = G.map (globeGenerator n)
  rw [ι_map, hx]

lemma globe_functor_equality (n : ℕ) {i : J} (G H : Functor (globe.{u} n) (F.obj i))
    (h : Functor.comp G ((cocone F).ι.app i) = Functor.comp H ((cocone F).ι.app i)) :
    ∃ (j : J) (f : i ⟶ j), Functor.comp G (F.map f) = Functor.comp H (F.map f) := by
  have he : ι F i (G.map (globeGenerator n)) = ι F i (H.map (globeGenerator n)) :=
    congrArg (fun G : Functor (globe.{u} n) (omega F) => G.map (globeGenerator n)) h
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (CellDiagram F)) _ _).mp he
  exact ⟨j, f, globe_functor_ext hf⟩

noncomputable def globeHomIsColimit (n : ℕ) :
    IsColimit ((coyoneda.obj (Opposite.op (globe.{u} n))).mapCocone (cocone F)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    obtain ⟨i, H, h⟩ := globe_functor_lift F n G
    exact ⟨i, H, h.symm⟩
  · intro i G H h
    exact globe_functor_equality F n G H h

instance globeHomPreservesColimit (n : ℕ) :
    PreservesColimit F (coyoneda.obj (Opposite.op (globe.{u} n))) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit F) (globeHomIsColimit F n)

end FilteredColimit

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance globe_finitelyPresentable (n : ℕ) :
    IsCardinalPresentable (globe.{u} n) Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
    exact ⟨fun {F} => inferInstance⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits Opposite

lemma injective_of_mono {C D : OmegaCategory.{u}} (F : C ⟶ D) [Mono F] :
    Function.Injective F.map := by
  intro x y hxy
  obtain ⟨p, hp⟩ := C.finite_dimension x
  obtain ⟨q, hq⟩ := C.finite_dimension y
  let n := max p q
  let G := globeLift n x (C.source_fixed_upwards (le_max_left p q) hp)
  let H := globeLift n y (C.source_fixed_upwards (le_max_right p q) hq)
  have h : G ≫ F = H ≫ F := globe_functor_ext hxy
  have he : G = H := (cancel_mono F).mp h
  exact congrArg (fun G : Functor (globe.{u} n) C => G.map (globeGenerator n)) he

lemma globes_separating : (ObjectProperty.ofObj (globe.{u})).IsSeparating := by
  intro C D F G h
  apply Functor.ext
  funext x
  obtain ⟨n, hn⟩ := C.finite_dimension x
  exact congrArg (fun H : Functor (globe.{u} n) D => H.map (globeGenerator n))
    (h (globe.{u} n) ⟨n⟩ (globeLift n x hn))

lemma globes_strongGenerator : (ObjectProperty.ofObj (globe.{u})).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨globes_separating, ?_⟩
  intro C D F _ h
  have hs : Function.Surjective F.map := by
    intro y
    obtain ⟨n, hn⟩ := D.finite_dimension y
    obtain ⟨G, hG⟩ := h (globe.{u} n) ⟨n⟩ (globeLift n y hn)
    exact ⟨G.map (globeGenerator n),
      congrArg (fun H : Functor (globe.{u} n) D => H.map (globeGenerator n)) hG⟩
  exact (isoOfBijective F ⟨injective_of_mono F, hs⟩).isIso_hom

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance locallyFinitelyPresentable :
    IsCardinalLocallyPresentable OmegaCategory.{u} Cardinal.aleph0.{u} := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨ObjectProperty.ofObj globe, inferInstance, globes_strongGenerator, ?_⟩
  rintro C ⟨n⟩
  exact globe_finitelyPresentable n

instance locallyPresentable : IsLocallyPresentable.{u} OmegaCategory.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance nCategory_locallyFinitelyPresentable (n : ℕ) :
    IsCardinalLocallyPresentable (NCategory.{u} n) Cardinal.aleph0.{u} :=
  (truncationAdjunction n).isCardinalLocallyPresentable Cardinal.aleph0.{u}

instance nCategory_locallyPresentable (n : ℕ) : IsLocallyPresentable.{u} (NCategory.{u} n) where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HornRealization
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFaithfulNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instFullNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetFinite_preservesFilteredColimits _root_.OAI.Thomason.streetNerveFiniteOne_faithful _root_.OAI.Thomason.streetNerveFiniteOne_full _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horn Realization. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory

instance thomasonWeakEquivalences_hasTwoOutOfThreeProperty :
    thomasonWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs (simplicialWeakEquivalences.inverseImage thomasonRight).HasTwoOutOfThreeProperty

instance thomasonWeakEquivalences_isStableUnderRetracts :
    thomasonWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs (simplicialWeakEquivalences.inverseImage thomasonRight).IsStableUnderRetracts

instance thomasonWeakEquivalencesFinite_hasTwoOutOfThreeProperty (n : ℕ) :
    (thomasonWeakEquivalencesFinite.{u} n).HasTwoOutOfThreeProperty :=
  inferInstanceAs
    (simplicialWeakEquivalences.inverseImage (thomasonRightFinite n)).HasTwoOutOfThreeProperty

instance thomasonWeakEquivalencesFinite_isStableUnderRetracts (n : ℕ) :
    (thomasonWeakEquivalencesFinite.{u} n).IsStableUnderRetracts :=
  inferInstanceAs
    (simplicialWeakEquivalences.inverseImage (thomasonRightFinite n)).IsStableUnderRetracts

end Thomason

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


namespace Thomason.GlobeComplex

open DirectedComplex

def complex (n : ℕ) : DirectedComplex.{u} where
  Chain := Chain n
  group _ := inferInstance
  d := differential n
  d_d p x := by
    change mass n (p+1) (mass n (p+2) x • delta n (p+1)) • delta n p = 0
    rw [map_zsmul, mass_delta, smul_zero, zero_smul]
  augmentation := mass n 0
  augmentation_d x := by
    change mass n 0 (mass n 1 x • delta n 0) = 0
    rw [map_zsmul, mass_delta, smul_zero]
  positive := positive n

lemma complex_d_coordinate (n p : ℕ) (x : (complex.{u} n).Chain (p+1)) (b : Bool) :
    ((complex n).d p x).val ⟨b⟩ = if b then mass n (p+1) x else -mass n (p+1) x :=
  differential_coordinate n p x b

lemma mass_nonneg {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) : 0 ≤ mass n p x :=
  add_nonneg (hx false) (hx true)

lemma coordinate_le_mass {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) (b : Bool) : x.val ⟨b⟩ ≤ mass n p x := by
  change x.val ⟨b⟩ ≤ x.val ⟨false⟩ + x.val ⟨true⟩
  cases b
  · linarith [hx true]
  · linarith [hx false]

lemma mass_eq_zero_iff {n p : ℕ} {x : (complex.{u} n).Chain p}
    (hx : x ∈ (complex n).positive p) : mass n p x = 0 ↔ x = 0 := by
  constructor
  · intro hm
    apply Subtype.ext
    funext ⟨b⟩
    have h := coordinate_le_mass hx b
    rw [hm] at h
    exact le_antisymm h (hx b)
  · rintro rfl
    exact map_zero _

def basis (n p : ℕ) (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)) :
    (complex.{u} n).Chain p :=
  ⟨fun i => if i.down = b then 1 else 0, by
    intro ⟨i⟩ hi
    dsimp
    split_ifs with h
    · subst i
      rcases hb with hb | ⟨hb, hb'⟩
      · rcases hi with hi | ⟨hi, _⟩ <;> omega
      · rcases hi with hi | ⟨_, hi⟩
        · omega
        · simp [hb'] at hi
    · rfl⟩

@[simp] lemma basis_coordinate (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) (i : Bool) :
    (basis.{u} n p b hb).val ⟨i⟩ = if i = b then 1 else 0 := rfl

@[simp] lemma mass_basis (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) : mass n p (basis.{u} n p b hb) = 1 := by
  cases b <;> simp [mass]

lemma basis_positive (n p : ℕ) (b : Bool)
    (hb : p < n ∨ (p = n ∧ b = false)) : basis.{u} n p b hb ∈ (complex n).positive p := by
  intro i
  simp only [basis_coordinate]
  split_ifs <;> omega

lemma differential_basis (n p : ℕ) (b : Bool)
    (hb : p+1 < n ∨ (p+1 = n ∧ b = false)) :
    (complex.{u} n).d p (basis n (p+1) b hb) =
      basis n p true (Or.inl (by rcases hb with hb | ⟨hb, _⟩ <;> omega)) -
      basis n p false (Or.inl (by rcases hb with hb | ⟨hb, _⟩ <;> omega)) := by
  apply Subtype.ext
  funext ⟨i⟩
  change ((complex n).d p _).val ⟨i⟩ = _
  rw [complex_d_coordinate, mass_basis]
  change (if i then (1 : ℤ) else -1) = (if i = true then 1 else 0) -
    (if i = false then 1 else 0)
  cases i <;> norm_num

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex DirectedComplex.Table

def topRow (n p : ℕ) (b : Bool) : (complex.{u} n).Chain p :=
  if h : p < n then basis n p b (Or.inl h)
  else if h : p = n then basis n p false (Or.inr ⟨h, rfl⟩) else 0

lemma topRow_lt (n p : ℕ) (b : Bool) (h : p < n) :
    topRow.{u} n p b = basis n p b (Or.inl h) := by simp [topRow, h]

lemma topRow_eq (n : ℕ) (b : Bool) :
    topRow.{u} n n b = basis n n false (Or.inr ⟨rfl, rfl⟩) := by simp [topRow]

lemma topRow_gt (n p : ℕ) (b : Bool) (h : n < p) : topRow.{u} n p b = 0 := by
  simp [topRow, show ¬p < n by omega, show p ≠ n by omega]

def topTable (n : ℕ) : Table (complex.{u} n) where
  row := topRow n
  positive p b := by
    unfold topRow
    split_ifs <;> first | exact basis_positive _ _ _ _ | exact (positive.{u} n p).zero_mem
  boundary p b := by
    by_cases hp : p < n
    · rw [topRow_lt n p true hp, topRow_lt n p false hp]
      by_cases hp' : p+1 < n
      · rw [topRow_lt n (p+1) b hp', differential_basis]
      · have he : p+1 = n := by omega
        rw [show topRow n (p+1) b = basis n (p+1) false (Or.inr ⟨he, rfl⟩) by
          unfold topRow; rw [dite_eq_right hp', dite_eq_left he]]
        exact differential_basis n p false (Or.inr ⟨he, rfl⟩)
    · rw [topRow_gt n (p+1) b (by omega), map_zero]
      by_cases he : p = n
      · subst p; rw [topRow_eq, topRow_eq, sub_self]
      · rw [topRow_gt n p true (by omega), topRow_gt n p false (by omega), sub_self]
  augmentation b := by
    change mass n 0 (topRow n 0 b) = 1
    unfold topRow
    split_ifs with h he
    · exact mass_basis _ _ _ _
    · exact mass_basis _ _ _ _
    · omega
  bounded := ⟨n, fun p hp b => topRow_gt n p b hp⟩

lemma topTable_bounded (n : ℕ) : truncate n false (topTable.{u} n) = topTable n := by
  ext p b
  rw [truncate_row]
  change (if p < n then topRow n p b else if p = n then topRow n p false else 0) = topRow n p b
  split_ifs with h he
  · rfl
  · subst p; rw [topRow_eq, topRow_eq]
  · exact (topRow_gt n p b (by omega)).symm

variable {n : ℕ} (x : Table (complex.{u} n))

lemma table_boundary_coordinate (p : ℕ) (b i : Bool) :
    (if i then mass n (p+1) (x.row (p+1) b) else -mass n (p+1) (x.row (p+1) b)) =
      (x.row p true).val ⟨i⟩ - (x.row p false).val ⟨i⟩ := by
  have h := congrArg (fun z : (complex n).Chain p => z.val ⟨i⟩) (x.boundary p b)
  rw [complex_d_coordinate] at h
  exact h

lemma table_mass_eq (p : ℕ) : mass n p (x.row p true) = mass n p (x.row p false) := by
  have h := congrArg (mass n p) (x.boundary p false)
  change mass n p (mass n (p+1) (x.row (p+1) false) • delta n p) = _ at h
  erw [map_sub, map_zsmul, mass_delta, smul_zero] at h
  omega

lemma table_mass_zero (b : Bool) : mass n 0 (x.row 0 b) = 1 := x.augmentation b

lemma table_mass_step (p : ℕ) (b : Bool) :
    mass n (p+1) (x.row (p+1) b) ≤ mass n p (x.row p false) := by
  have h := table_boundary_coordinate x p b false
  simp only [Bool.false_eq_true, ite_false] at h
  have hp := x.positive p true false
  have hc := coordinate_le_mass (x.positive p false) false
  omega

lemma table_mass_le_one (p : ℕ) (b : Bool) : mass n p (x.row p b) ≤ 1 := by
  induction p generalizing b with
  | zero => rw [table_mass_zero]
  | succ p ih => exact (table_mass_step x p b).trans (ih false)

lemma table_mass_antitone : Antitone (fun p => mass n p (x.row p false)) := by
  apply antitone_nat_of_succ_le
  intro p
  exact table_mass_step x p false

lemma positive_mass_one {p : ℕ} (z : (complex.{u} n).Chain p)
    (hz : z ∈ (complex n).positive p) (hm : mass n p z = 1) :
    ∃ (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)), z = basis n p b hb := by
  have hp : p ≤ n := by
    by_contra h
    rw [chain_zero (by omega) z, map_zero] at hm
    omega
  have h₀ := hz false
  have h₁ := hz true
  change z.val ⟨false⟩ + z.val ⟨true⟩ = 1 at hm
  by_cases h : z.val ⟨false⟩ = 1
  · have hb : p < n ∨ (p = n ∧ false = false) := by
      by_cases h : p < n
      · exact Or.inl h
      · exact Or.inr ⟨by omega, rfl⟩
    refine ⟨false, hb, ?_⟩
    apply Subtype.ext
    funext ⟨i⟩
    change z.val ⟨i⟩ = if i = false then 1 else 0
    cases i <;> dsimp <;> omega
  · have ht : z.val ⟨true⟩ = 1 := by omega
    have hpn : p < n := by
      by_contra hpn
      have he : p = n := by omega
      subst p
      have := top_target_zero n z
      omega
    refine ⟨true, Or.inl hpn, ?_⟩
    apply Subtype.ext
    funext ⟨i⟩
    change z.val ⟨i⟩ = if i = true then 1 else 0
    cases i <;> dsimp <;> omega

lemma table_has_top : ∃ p, p ≤ n ∧ mass n p (x.row p false) = 1 ∧
    ∀ q, p < q → ∀ b, x.row q b = 0 := by
  classical
  let s := (Finset.range (n+1)).filter (fun p => mass n p (x.row p false) ≠ 0)
  have he : s.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), by rw [table_mass_zero]; omega⟩⟩
  let p := s.max' he
  have hp : p ∈ s := Finset.max'_mem s he
  obtain ⟨hpn, hpne⟩ := Finset.mem_filter.mp hp
  have hple : p ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hpn
  have hpmass : mass n p (x.row p false) = 1 := by
    have := table_mass_le_one x p false
    have := mass_nonneg (x.positive p false)
    omega
  refine ⟨p, hple, hpmass, ?_⟩
  intro q hpq b
  have hqzero : mass n q (x.row q false) = 0 := by
    by_contra hq
    have hqn : q ≤ n := by
      by_contra h
      exact hq (by rw [chain_zero (by omega) (x.row q false), map_zero])
    have hqmem : q ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
    have := Finset.le_max' s q hqmem
    omega
  apply (mass_eq_zero_iff (x.positive q b)).mp
  cases b
  · exact hqzero
  · rw [table_mass_eq, hqzero]

lemma table_lower_row {p : ℕ} (hm : mass n (p+1) (x.row (p+1) false) = 1)
    (hp : p < n) (b : Bool) : x.row p b = basis n p b (Or.inl hp) := by
  have h₀ := table_boundary_coordinate x p false false
  have h₁ := table_boundary_coordinate x p false true
  simp only [Bool.false_eq_true, ite_false, ite_true, hm] at h₀ h₁
  have hs := table_mass_le_one x p false
  have ht := table_mass_le_one x p true
  change (x.row p false).val ⟨false⟩ + (x.row p false).val ⟨true⟩ ≤ 1 at hs
  change (x.row p true).val ⟨false⟩ + (x.row p true).val ⟨true⟩ ≤ 1 at ht
  have hsf := x.positive p false false
  have hst := x.positive p false true
  have htf := x.positive p true false
  have htt := x.positive p true true
  apply Subtype.ext
  funext ⟨i⟩
  change (x.row p b).val ⟨i⟩ = if i = b then 1 else 0
  cases b <;> cases i <;> dsimp <;> omega

lemma topRow_basis {p : ℕ} (b : Bool) (hb : p < n ∨ (p = n ∧ b = false)) :
    topRow.{u} n p b = basis n p b hb := by
  rcases hb with h | ⟨rfl, rfl⟩
  · rw [topRow_lt n p b h]
  · rw [topRow_eq]

lemma table_classification : ∃ (p : ℕ) (b : Bool), p ≤ n ∧
    x = truncate p b (topTable n) := by
  obtain ⟨p, hpn, hmass, hzero⟩ := table_has_top x
  obtain ⟨b, hb, he⟩ := positive_mass_one (x.row p false) (x.positive p false) hmass
  have hpeq : x.row p true = x.row p false := by
    have h := x.boundary p false
    rw [hzero (p+1) (by omega) false, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  refine ⟨p, b, hpn, ?_⟩
  ext q a
  rw [truncate_row]
  by_cases hq : q < p
  · rw [ite_eq_left hq]
    have hm : mass n (q+1) (x.row (q+1) false) = 1 := by
      have hupper := table_mass_le_one x (q+1) false
      have hlower := table_mass_antitone x (show q+1 ≤ p by omega)
      change mass n p (x.row p false) ≤ mass n (q+1) (x.row (q+1) false) at hlower
      rw [hmass] at hlower
      omega
    rw [table_lower_row x hm (by omega)]
    exact (topRow_lt n q a (by omega)).symm
  · rw [ite_eq_right hq]
    by_cases heq : q = p
    · subst q
      rw [ite_eq_left rfl]
      change x.row p a = topRow n p b
      rw [topRow_basis b hb]
      cases a
      · exact he
      · exact hpeq.trans he
    · rw [ite_eq_right heq]
      exact hzero q (by omega) a

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex DirectedComplex.Table OmegaCategory

lemma top_face_mass {n p : ℕ} (hp : p ≤ n) (b : Bool) :
    mass n p ((truncate p b (topTable.{u} n)).row p false) = 1 := by
  rw [truncate_top_row]
  change mass n p (topRow n p b) = 1
  by_cases h : p < n
  · rw [topRow_lt n p b h, mass_basis]
  · have he : p = n := by omega
    subst p; rw [topRow_eq, mass_basis]

lemma top_face_dimension {n p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (a b : Bool)
    (h : truncate p a (topTable.{u} n) = truncate q b (topTable n)) : p = q := by
  by_contra he
  rcases lt_or_gt_of_ne he with hpq | hqp
  · have hh := congrArg (fun t : Table (complex n) => mass n q (t.row q false)) h
    erw [truncate_row, ite_eq_right (by omega), ite_eq_right (by omega), map_zero,
      top_face_mass hq b] at hh
    omega
  · have hh := congrArg (fun t : Table (complex n) => mass n p (t.row p false)) h
    erw [top_face_mass hp a, truncate_row, ite_eq_right (by omega), ite_eq_right (by omega), map_zero] at hh
    omega

lemma top_face_sign {n p : ℕ} (hp : p < n) (a b : Bool)
    (h : truncate p a (topTable.{u} n) = truncate p b (topTable n)) : a = b := by
  have hh := congrArg (fun t : Table (complex n) => (t.row p false).val ⟨a⟩) h
  rw [truncate_top_row, truncate_top_row] at hh
  change (topRow n p a).val ⟨a⟩ = (topRow n p b).val ⟨a⟩ at hh
  rw [topRow_lt n p a hp, topRow_lt n p b hp] at hh
  change (if a = a then (1 : ℤ) else 0) = (if a = b then 1 else 0) at hh
  simp only [ite_true] at hh
  split_ifs at hh with he
  · exact he
  · omega

lemma composable_has_identity {n : ℕ} (k : ℕ) (x y : Table (complex.{u} n))
    (h : truncate k true x = truncate k false y) :
    truncate k false x = x ∨ truncate k false y = y := by
  obtain ⟨p, a, hpn, rfl⟩ := table_classification x
  obtain ⟨q, b, hqn, rfl⟩ := table_classification y
  by_cases hkp : k < p
  · by_cases hkq : k < q
    · rw [truncate_truncate, truncate_truncate, ite_eq_left hkp, ite_eq_left hkq] at h
      have := top_face_sign (by omega : k < n) true false h
      cases this
    · exact Or.inr (by rw [truncate_truncate, ite_eq_right hkq])
  · exact Or.inl (by rw [truncate_truncate, ite_eq_right hkp])

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex OmegaCategory

lemma basisLambda_positive {E : Type u} [PartialOrder E] (p : ℕ) (w : Word E) :
    basisLambda p w ∈ (complex E).nu.lambdaPositive p := by
  classical
  unfold basisLambda
  split_ifs with h
  · rcases w with ⟨w, hw⟩
    cases w with
    | nil => exact False.elim (by change 0 = p + 1 at h; omega)
    | cons a l => exact (complex E).nu.lambdaGen_positive _
  · exact AddSubmonoid.zero_mem _

lemma atomCounitInverse_positive {E : Type u} [PartialOrder E] (p : ℕ)
    (x : (complex E).Chain p) (hx : x ∈ (complex E).positive p) :
    atomCounitInverse p x ∈ (complex E).nu.lambdaPositive p := by
  classical
  change Finsupp.linearCombination ℤ (basisLambda p) x.val ∈ _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply AddSubmonoid.sum_mem
  intro w _
  have hw : 0 ≤ x.val w := hx w
  have he : x.val w = (x.val w).toNat := (Int.toNat_of_nonneg hw).symm
  rw [he, Nat.cast_smul_eq_nsmul]
  exact AddSubmonoid.nsmul_mem _ (basisLambda_positive p w) _

lemma oriental_lambdaCounit_rightInverse {N : ℕ} (p : ℕ) :
    ((complex (Fin (N+1))).lambdaCounitMap p).comp (atomCounitInverse p) =
      LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := normalized_lambdaCounit_surjective (E := Fin (N+1)) p x
  exact congrArg ((complex (Fin (N+1))).lambdaCounitMap p)
    (LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) y)

lemma counit_atomInverse {N : ℕ} (p : ℕ) (x : (complex (Fin (N+1))).Chain p) :
    (complex (Fin (N+1))).lambdaCounitMap p (atomCounitInverse p x) = x :=
  LinearMap.congr_fun (oriental_lambdaCounit_rightInverse p) x

noncomputable def simplexCounitInverse (N : ℕ) :
    Hom (complex (Fin (N+1))) (complex (Fin (N+1))).nu.linearization where
  map p := (atomCounitInverse p).toAddMonoidHom
  map_d p x := by
    apply oriental_lambdaCounit_injective p
    calc
      _ = (complex (Fin (N+1))).d p x := counit_atomInverse p _
      _ = (complex (Fin (N+1))).d p
          ((complex (Fin (N+1))).lambdaCounitMap (p+1) (atomCounitInverse (p+1) x)) :=
        congrArg ((complex (Fin (N+1))).d p) (counit_atomInverse (p+1) x).symm
      _ = _ := (DFunLike.congr_fun ((complex (Fin (N+1))).lambdaCounitMap_d p)
        (atomCounitInverse (p+1) x)).symm
  map_augmentation x := by
    exact (DFunLike.congr_fun (complex (Fin (N+1))).lambdaCounitMap_aug
      (atomCounitInverse 0 x)).symm.trans
      (congrArg (complex (Fin (N+1))).augmentation (counit_atomInverse 0 x))
  map_positive := atomCounitInverse_positive

lemma simplexCounitInverse_counit (N : ℕ) :
    Hom.comp (simplexCounitInverse N) (complex (Fin (N+1))).lambdaCounit =
      Hom.id (complex (Fin (N+1))) := by
  ext p x
  exact LinearMap.congr_fun (oriental_lambdaCounit_rightInverse p) x

lemma counit_simplexCounitInverse (N : ℕ) :
    Hom.comp (complex (Fin (N+1))).lambdaCounit (simplexCounitInverse N) =
      Hom.id (complex (Fin (N+1))).nu.linearization := by
  ext p x
  exact LinearMap.congr_fun (oriental_lambdaCounit_leftInverse p) x

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BoundaryQuotients
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Quotients. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma truncationLambdaRetraction_leftInverse (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    (truncationLambdaRetraction C n p hp).comp ((truncationUnit n C).lambdaMap p) = LinearMap.id := by
  apply C.lambda_linear_ext
  intro x
  change truncationLambdaRetraction C n p hp
    ((truncationUnit n C).lambdaMap p (C.lambdaGen x)) = C.lambdaGen x
  rw [Functor.lambdaMap_gen]
  exact (truncationLambdaRetraction_gen C n p hp ((truncationUnit n C).onCells p x)).trans
    (congrArg C.lambdaGen (truncationCellLift_of_unit C n p hp x))

lemma truncationUnit_lambdaMap_injective (C : OmegaCategory.{u}) (n p : ℕ) (hp : p < n) :
    Function.Injective ((truncationUnit n C).lambdaMap p) := by
  intro x y h
  have hx := LinearMap.congr_fun (truncationLambdaRetraction_leftInverse C n p hp) x
  have hy := LinearMap.congr_fun (truncationLambdaRetraction_leftInverse C n p hp) y
  exact hx.symm.trans ((congrArg (truncationLambdaRetraction C n p hp) h).trans hy)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory

variable {C : OmegaCategory.{u}} {n N : ℕ}

def liftedBasis (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) : C.LambdaChain p := by
  classical
  by_cases h : w.val.length = p+1
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      let A := simplexAtom a l (hw.imp le_of_lt)
      have he : (a::l).length-1 = p := by simp only [List.length_cons] at h ⊢; omega
      exact C.lambdaGen (truncationCellLift C n p (F.onCells p ⟨A.table, he ▸ A.dimension⟩))
  · exact 0

lemma liftedBasis_cons (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (h : l.length = p)
    (hd : truncate p false (simplexAtom a l (ha.imp le_of_lt)).table =
      (simplexAtom a l (ha.imp le_of_lt)).table) :
    liftedBasis F p ⟨a::l,ha⟩ = C.lambdaGen
      (truncationCellLift C n p (F.onCells p ⟨_,hd⟩)) := by
  simp [liftedBasis,h]

lemma liftedBasis_unit (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) :
    (truncationUnit n C).lambdaMap p (liftedBasis F p w) = F.lambdaMap p (basisLambda p w) := by
  classical
  unfold liftedBasis basisLambda
  split_ifs with h
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l =>
      erw [OmegaCategory.Functor.lambdaMap_gen, OmegaCategory.Functor.lambdaMap_gen]
      congr 1
      exact truncationCellLift_unit C n p _
  · exact (map_zero ((truncationUnit n C).lambdaMap p)).trans (map_zero (F.lambdaMap p)).symm

def liftedChainMap (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) : (complex (Fin (N+1))).Chain p →ₗ[ℤ] C.LambdaChain p :=
  (Finsupp.linearCombination ℤ (liftedBasis F p)).comp (grade (p+1)).subtype

lemma liftedChainMap_bracket (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) (h : w.val.length = p+1) :
    liftedChainMap F p ⟨bracket w.val, h ▸ bracket_mem_grade w.val⟩ = liftedBasis F p w := by
  change Finsupp.linearCombination ℤ (liftedBasis F p) (bracket w.val) = _
  rw [bracket_of_pairwise w.property,Finsupp.linearCombination_single,one_smul]

lemma liftedChainMap_unit (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (x : (complex (Fin (N+1))).Chain p) :
    (truncationUnit n C).lambdaMap p (liftedChainMap F p x) =
      F.lambdaMap p (atomCounitInverse p x) := by
  change ((truncationUnit n C).lambdaMap p).comp
      (Finsupp.linearCombination ℤ (liftedBasis F p)) x.val =
    (F.lambdaMap p).comp (Finsupp.linearCombination ℤ (basisLambda p)) x.val
  congr 1
  apply Finsupp.lhom_ext
  intro w z
  change (truncationUnit n C).lambdaMap p
    (Finsupp.linearCombination ℤ (liftedBasis F p) (Finsupp.single w z)) =
    F.lambdaMap p (Finsupp.linearCombination ℤ (basisLambda p) (Finsupp.single w z))
  erw [Finsupp.linearCombination_single,Finsupp.linearCombination_single,map_smul,map_smul,
    liftedBasis_unit]
  rfl

lemma liftedChainMap_aug (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (x : (complex (Fin (N+1))).Chain 0) :
    C.lambdaAug (liftedChainMap F 0 x) = (complex (Fin (N+1))).augmentation x := by
  calc
    _ = (truncation n C).val.lambdaAug
        ((truncationUnit n C).lambdaMap 0 (liftedChainMap F 0 x)) :=
      (LinearMap.congr_fun ((truncationUnit n C).lambdaMap_aug) _).symm
    _ = (truncation n C).val.lambdaAug (F.lambdaMap 0 (atomCounitInverse 0 x)) :=
      congrArg _ (liftedChainMap_unit F 0 x)
    _ = (Oriental N).lambdaAug (atomCounitInverse 0 x) :=
      LinearMap.congr_fun F.lambdaMap_aug _
    _ = _ := (simplexCounitInverse N).map_augmentation x

lemma liftedBasis_positive (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (w : Word (Fin (N+1))) : liftedBasis F p w ∈ C.lambdaPositive p := by
  classical
  unfold liftedBasis
  split_ifs with h
  · rcases w with ⟨w,hw⟩
    cases w with
    | nil => simp at h
    | cons a l => exact C.lambdaGen_positive _
  · exact AddSubmonoid.zero_mem _

lemma liftedChainMap_positive (F : OmegaCategory.Functor (Oriental N) (truncation n C).val)
    (p : ℕ) (x : (complex (Fin (N+1))).Chain p) (hx : x ∈ (complex (Fin (N+1))).positive p) :
    liftedChainMap F p x ∈ C.lambdaPositive p := by
  classical
  change Finsupp.linearCombination ℤ (liftedBasis F p) x.val ∈ _
  rw [Finsupp.linearCombination_apply,Finsupp.sum]
  apply AddSubmonoid.sum_mem
  intro w _
  have hw : 0 ≤ x.val w := hx w
  have he : x.val w = (x.val w).toNat := (Int.toNat_of_nonneg hw).symm
  rw [he,Nat.cast_smul_eq_nsmul]
  exact AddSubmonoid.nsmul_mem _ (liftedBasis_positive F p w) _

lemma atomCounitInverse_row (p : ℕ) (y : Table (complex (Fin (N+1)))) (b : Bool) :
    atomCounitInverse p (y.row p b) = (Oriental N).lambdaGen
      (if b then (Oriental N).targetCell p y else (Oriental N).sourceCell p y) := by
  have h := atomCounitInverse_top (p := p) (truncate p b y) (by simp only [truncate_truncate,lt_self_iff_false,ite_false])
  rw [truncate_top_row] at h
  cases b <;> exact h

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SkeletalCategories
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.street_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skeletal Categories. -/

noncomputable section
universe u v w z


namespace Thomason

open DirectedComplex NormalizedChains OmegaCategory

lemma lambdaNuForward_counit {K : DirectedComplex.{u}} {L : DirectedComplex.{v}}
    (f : Hom K L) : lambdaNuForward (Hom.comp K.lambdaCounit f) = f.nu := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Table.ext
  funext p b
  cases b
  · change f.map p (K.lambdaCounitMap p (K.nu.lambdaGen (K.nu.sourceCell p x))) = f.map p (x.row p false)
    rw [K.lambdaCounitMap_gen]
    exact congrArg (f.map p) (Table.truncate_top_row p false x false)
  · change f.map p (K.lambdaCounitMap p (K.nu.lambdaGen (K.nu.targetCell p x))) = f.map p (x.row p true)
    rw [K.lambdaCounitMap_gen]
    exact congrArg (f.map p) (Table.truncate_top_row p true x false)

noncomputable def orientalChain (N : ℕ) {K : DirectedComplex.{u}}
    (F : OmegaCategory.Functor (Oriental N) K.nu) : Hom (complex (Fin (N+1))) K :=
  Hom.comp (simplexCounitInverse N) (lambdaNuBackward F)

lemma orientalChain_nu (N : ℕ) {K : DirectedComplex.{u}}
    (F : OmegaCategory.Functor (Oriental N) K.nu) : (orientalChain N F).nu = F := by
  rw [← lambdaNuForward_counit]
  change lambdaNuForward (Hom.comp
    (Hom.comp (complex (Fin (N+1))).lambdaCounit (simplexCounitInverse N))
    (lambdaNuBackward F)) = F
  rw [counit_simplexCounitInverse]
  exact lambdaNu_right_inv F

lemma orientalChain_of_nu (N : ℕ) {K : DirectedComplex.{u}}
    (f : Hom (complex (Fin (N+1))) K) : orientalChain N f.nu = f := by
  unfold orientalChain
  rw [← lambdaNuForward_counit f, lambdaNu_left_inv]
  change Hom.comp (Hom.comp (simplexCounitInverse N)
    (complex (Fin (N+1))).lambdaCounit) f = f
  rw [simplexCounitInverse_counit]
  rfl

lemma oriental_nu_injective {N : ℕ} {K : DirectedComplex.{u}}
    {f g : Hom (complex (Fin (N+1))) K} (h : f.nu = g.nu) : f = g := by
  simpa only [orientalChain_of_nu] using congrArg (orientalChain N) h

lemma orientalChain_natural {m n : ℕ} {K : DirectedComplex.{u}}
    (a : Fin (m+1) →o Fin (n+1)) (F : OmegaCategory.Functor (Oriental n) K.nu) :
    orientalChain m (OmegaCategory.Functor.comp (complexMap a).nu F) =
      Hom.comp (complexMap a) (orientalChain n F) := by
  apply oriental_nu_injective
  rw [orientalChain_nu]
  change OmegaCategory.Functor.comp (complexMap a).nu F =
    OmegaCategory.Functor.comp (complexMap a).nu (orientalChain n F).nu
  rw [orientalChain_nu]

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory DirectedComplex

lemma simplicialWeakEquivalence_of_simplicial_retract {X Y : SSet.{u}} (f : X ⟶ Y)
    (g : Y ⟶ X) (hr : g ≫ f = 𝟙 Y) (H : SSet.Homotopy (𝟙 X) (f ≫ g)) :
    simplicialWeakEquivalences f := by
  have hw := (simplicialWeakEquivalences_homotopy H).mp (simplicialWeakEquivalences.id_mem X)
  have hret : RetractArrow f (f ≫ g) :=
    { i := Arrow.homMk (𝟙 X) g (by change 𝟙 X ≫ (f ≫ g) = f ≫ g; simp)
      r := Arrow.homMk (𝟙 X) f (by change 𝟙 X ≫ f = (f ≫ g) ≫ f; simp [Category.assoc,hr])
      retract := by ext <;> simp [hr] }
  exact simplicialWeakEquivalences.of_retract hret hw

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionFaces
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.streetFinite_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Faces. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory Opposite

instance categorificationFiniteOne_counit_iso :
    IsIso (categorificationFiniteAdjunction.{u} 1).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionWeak
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.instEssSurjNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.instIsEquivalenceNCategoryOfNatNatCatOneSkeletonCatFunctor _root_.OAI.Thomason.OmegaCategory.oneFiberFinite_preservesColimits _root_.OAI.Thomason.OmegaCategory.opFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.reverseLabelFiniteFunctor_isEquivalence _root_.OAI.Thomason.OmegaCategory.zeroFiberFinite_preservesColimits _root_.OAI.Thomason.OneCat.oneUnitCatIso _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance thomasonRight_preservesFilteredColimits :
    PreservesFilteredColimits thomasonRight.{u} := by
  unfold thomasonRight
  infer_instance

instance thomasonFiniteRight_preservesFiltered (n : ℕ) :
    PreservesFilteredColimits (thomasonRightFinite.{u} n) := by
  unfold thomasonRightFinite
  infer_instance

instance thomasonRight_finitelyAccessible : Functor.IsFinitelyAccessible.{u} thomasonRight.{u} :=
  Functor.isFinitelyAccessible_iff_preservesFilteredColimits.mpr inferInstance

instance thomasonRightFinite_finitelyAccessible (n : ℕ) :
    Functor.IsFinitelyAccessible.{u} (thomasonRightFinite.{u} n) :=
  Functor.isFinitelyAccessible_iff_preservesFilteredColimits.mpr inferInstance

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance thomasonLeft_finitelyPresentable (X : SSet.{u}) [X.Finite] :
    IsFinitelyPresentable.{u} (thomasonLeft.obj X) :=
  thomasonAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 X

instance thomasonLeftFinite_finitelyPresentable (n : ℕ) (X : SSet.{u}) [X.Finite] :
    IsFinitelyPresentable.{u} ((thomasonLeftFinite n).obj X) :=
  (thomasonFiniteAdjunction n).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 X

end Thomason

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


namespace Thomason

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance thomasonBoundary_smallCardinal :
    IsCardinalForSmallObjectArgument (boundaryImages thomasonLeft.{u}) Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance thomasonHorn_smallCardinal :
    IsCardinalForSmallObjectArgument (hornImages thomasonLeft.{u}) Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [hornImages, iSup_iff] at hi
      obtain ⟨n, ⟨j⟩⟩ := hi
      infer_instance
    infer_instance

instance thomasonBoundaryFinite_smallCardinal (n : ℕ) :
    IsCardinalForSmallObjectArgument (boundaryImages (thomasonLeftFinite.{u} n))
      Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨m⟩ := hi
      infer_instance
    infer_instance

instance thomasonHornFinite_smallCardinal (n : ℕ) :
    IsCardinalForSmallObjectArgument (hornImages (thomasonLeftFinite.{u} n))
      Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [hornImages, iSup_iff] at hi
      obtain ⟨m, ⟨j⟩⟩ := hi
      infer_instance
    infer_instance

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma positive_cycle_zero_partial {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2))
    (hp : Positive c) (hd : boundary c = 0) : c = 0 := by
  let f := toLinearExtension (α := E)
  apply map_injectiveOrderHom_injective f (fun _ _ h => h)
  rw [map_zero]
  apply positive_cycle_zero (map_mem_grade f hc) (map_positive f hp)
  rw [← map_boundary, hd, map_zero]

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LabelledFibers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso
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

lemma labelled_pushout_fibers {A B C D : Over interval.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f.left g.left h.left i.left) (e : Fin 2) :
    IsPushout ((fiberFunctor (intervalVertex e)).map f)
      ((fiberFunctor (intervalVertex e)).map g)
      ((fiberFunctor (intervalVertex e)).map h)
      ((fiberFunctor (intervalVertex e)).map i) := by
  have hp : IsPushout f g h i := H.of_map_of_faithful (Over.forget interval)
  fin_cases e
  · exact hp.map (fiberFunctor (intervalVertex 0))
  · exact hp.map (fiberFunctor (intervalVertex 1))

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}}

def maxLabel (p q : Functor C interval.{u}) : Functor C interval.{u} where
  map x := ⟨⟨max (p.map x).left.down (q.map x).left.down⟩,
    ⟨max (p.map x).right.down (q.map x).right.down⟩,
    max_le_max (p.map x).related (q.map x).related⟩
  map_source k x := by
    rw [p.map_source, q.map_source]
    cases k <;> rfl
  map_target k x := by
    rw [p.map_target, q.map_target]
    cases k <;> rfl
  map_comp k x y h h' := by
    rw [p.map_comp k x y h (p.map_composable h), q.map_comp k x y h (q.map_composable h)]
    cases k <;> rfl

lemma maxLabel_zero_fiber (p q : Functor C interval.{u}) :
    ((maxLabel p q).fiber (intervalVertex 0)).carrier =
      (p.fiber (intervalVertex 0)).carrier ∩ (q.fiber (intervalVertex 0)).carrier := by
  ext x
  change (maxLabel p q).map x = (intervalVertex 0).val ↔
    p.map x = (intervalVertex 0).val ∧ q.map x = (intervalVertex 0).val
  simp only [intervalCell_eq_vertex_iff]
  rcases interval_cases (p.map x) with hp | hp | hp <;>
    rcases interval_cases (q.map x) with hq | hq | hq <;>
    simp [maxLabel, hp, hq, intervalVertex, intervalArrow]

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexColimits
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex DirectedComplex.Table
variable {E : Type u} [PartialOrder E]

lemma simplexAtom_source_zero (a : E) (l : List E)
    (h : (a :: l).Pairwise (· ≤ ·)) :
    ((simplexAtom a l h).table.row 0 false).val = bracket [a] := by
  cases l <;> rfl

lemma simplexAtom_vertices_supported {S : Set E} (a : E) (l : List E)
    (h : (a :: l).Pairwise (· < ·))
    (h0 : ((simplexAtom a l (h.imp le_of_lt)).table.row 0 false).val ∈ supportedOn S)
    (h1 : ((simplexAtom a l (h.imp le_of_lt)).table.row 1 true).val ∈ supportedOn S) :
    ∀ b ∈ a :: l, b ∈ S := by
  have ha : a ∈ S := (vertex_supportedOn_iff a S).mp (by simpa [simplexAtom_source_zero] using h0)
  induction l generalizing a with
  | nil => simpa using ha
  | cons b l ih =>
    have hb : a < b := (List.pairwise_cons.mp h).1 b (by simp)
    have he : ((simplexAtom a (b :: l) (h.imp le_of_lt)).table.row 1 true).val =
        ((simplexAtom b l (h.tail.imp le_of_lt)).table.row 1 true).val + bracket [a,b] := by
      change _ + prepend a ((simplexAtom b l (h.tail.imp le_of_lt)).table.row 0 false).val = _
      erw [simplexAtom_source_zero, prepend_bracket]
    rw [he] at h1
    obtain ⟨ht,he⟩ := supportedOn_of_add_positive
      ((simplexAtom b l (h.tail.imp le_of_lt)).table.positive 1 true)
      (bracket_positive [a,b]) h1
    have hbs : b ∈ S := ((edge_supportedOn_iff hb S).mp he).2
    have htail := ih b h.tail
      (by rw [simplexAtom_source_zero]; exact (vertex_supportedOn_iff b S).mpr hbs) ht hbs
    simpa using List.forall_mem_cons.mpr ⟨ha, htail⟩

lemma table_finish_supported {S : Set E} (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    (x.row 0 true).val ∈ supportedOn S := by
  have he := congrArg Subtype.val (x.boundary 0 true)
  change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
  rw [eq_sub_iff_add_eq] at he
  rw [← he]
  exact (supportedOn S).add_mem (boundary_mem_supportedOn h1) h0

lemma oriental_support_of_target {N : ℕ} (S : Set (Fin (N+1))) (x : Table (complex (Fin (N+1))))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  have hx := oriental_all_atomic x
  induction hx with
  | atom a l h =>
    intro p b
    exact supportedOn_mono (simplexAtom_vertices_supported a l h h0 h1)
      ((simplexAtom a l (h.imp le_of_lt)).supported p b)
  | compose k x y h hx hy ihx ihy =>
    have h0x : (x.row 0 false).val ∈ supportedOn S := by
      cases k with
      | zero => exact h0
      | succ k => simpa only [comp_row, Nat.zero_lt_succ, ite_true] using h0
    have h1y : (y.row 1 true).val ∈ supportedOn S := by
      cases k with
      | zero =>
        have hh : (x.row 1 true).val + (y.row 1 true).val ∈ supportedOn S := by
          exact h1
        exact (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) hh).2
      | succ k =>
        cases k with
        | zero => simpa using h1
        | succ k =>
          have he := lower_rows_eq h (show 1 < k+1+1 by omega) true
          simpa [show 1 < k+1+1 by omega, he] using h1
    have hxy : ∀ p b, (x.row p b).val ∈ supportedOn S ∧ (y.row p b).val ∈ supportedOn S := by
      cases k with
      | zero =>
        have h1x : (x.row 1 true).val ∈ supportedOn S :=
          (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true)
            h1).1
        have h0y : (y.row 0 false).val ∈ supportedOn S := by
          rw [← matching_row_eq h]
          exact table_finish_supported x h0x h1x
        exact fun p b => ⟨ihx h0x h1x p b, ihy h0y h1y p b⟩
      | succ k =>
        have h0y : (y.row 0 false).val ∈ supportedOn S := by
          rw [← lower_rows_eq h (Nat.zero_lt_succ k) false]
          exact h0x
        have hy' := ihy h0y h1y
        have h1x : (x.row 1 true).val ∈ supportedOn S := by
          cases k with
          | zero => rw [matching_row_eq h]; exact hy' 1 false
          | succ k =>
            rw [lower_rows_eq h (show 1 < k+1+1 by omega) true]
            exact h1y
        exact fun p b => ⟨ihx h0x h1x p b, hy' p b⟩
    intro p b
    simp only [Table.comp_row]
    split_ifs
    · exact (hxy p b).1
    · exact (hxy p true).2
    · exact (hxy p false).1
    · exact (supportedOn S).add_mem (hxy p b).1 (hxy p b).2

lemma table_support_of_target_finite [Finite E] (S : Set E) (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  classical
  let : Nonempty E := ⟨(table_zero_row_vertex x false).choose⟩
  let : Fintype E := Fintype.ofFinite E
  let : Fintype (LinearExtension E) := inferInstanceAs (Fintype E)
  let : Nonempty (LinearExtension E) := inferInstanceAs (Nonempty E)
  let n := Fintype.card (LinearExtension E) - 1
  have hn : Fintype.card (LinearExtension E) = n+1 := by
    have := Fintype.card_pos (α := LinearExtension E)
    dsimp only [n]
    omega
  let e : Fin (n+1) ≃o LinearExtension E := Fintype.orderIsoFinOfCardEq (LinearExtension E) hn
  let f : E →o Fin (n+1) := e.symm.toOrderEmbedding.toOrderHom.comp toLinearExtension
  have hf : Function.Injective f := e.symm.injective.comp (fun _ _ h => h)
  have hS : f ⁻¹' (f '' S) = S := Set.preimage_image_eq _ hf
  have hm : ∀ p b, map f (x.row p b).val ∈ supportedOn (f '' S) :=
    oriental_support_of_target (f '' S) ((complexMap f).table x)
      (map_supportedOn f (S := S) (T := f '' S) (fun a ha => ⟨a,ha,rfl⟩) h0)
      (map_supportedOn f (S := S) (T := f '' S) (fun a ha => ⟨a,ha,rfl⟩) h1)
  intro p b
  rw [← hS]
  exact supportedOn_of_injective_map f hf (hm p b)

lemma table_finite_support (x : Table (complex E)) :
    ∃ S : Finset E, ∀ p b, (x.row p b).val ∈ supportedOn (S : Set E) := by
  classical
  obtain ⟨n, hn⟩ := x.bounded
  let S := (Finset.range (n+1)).biUnion fun p => (Finset.univ : Finset Bool).biUnion fun b =>
    (x.row p b).val.support.biUnion fun w => w.val.toFinset
  refine ⟨S, ?_⟩
  intro p b
  rw [mem_supportedOn_iff]
  intro w hw a ha
  have hp : p < n+1 := by
    by_contra h
    have hnp : n < p := by omega
    have hz := congrArg Subtype.val (hn p hnp b)
    change (x.row p b).val = 0 at hz
    rw [hz] at hw
    exact hw rfl
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_range.mpr hp,
    Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b,
      Finset.mem_biUnion.mpr ⟨w, Finsupp.mem_support_iff.mpr hw, List.mem_toFinset.mpr ha⟩⟩⟩

lemma table_support_of_target (S : Set E) (x : Table (complex E))
    (h0 : (x.row 0 false).val ∈ supportedOn S)
    (h1 : (x.row 1 true).val ∈ supportedOn S) :
    ∀ p b, (x.row p b).val ∈ supportedOn S := by
  classical
  obtain ⟨T, hT⟩ := table_finite_support x
  let : Finite (Subtype (T : Set E)) := T.finite_toSet.to_subtype
  let y := restrictTable (T : Set E) x hT
  let i : ↥(T : Set E) →o E := (OrderEmbedding.subtype (T : Set E)).toOrderHom
  have hm (p : ℕ) (b : Bool) : map i (y.row p b).val = (x.row p b).val :=
    congrArg (fun z => (z.row p b).val) (table_map_restrictTable (T : Set E) x hT)
  have hy : ∀ p b, (y.row p b).val ∈ supportedOn (i ⁻¹' S) :=
    table_support_of_target_finite (E := ↥(T : Set E)) (i ⁻¹' S) y
      (supportedOn_of_injective_map i Subtype.val_injective (by rw [hm]; exact h0))
      (supportedOn_of_injective_map i Subtype.val_injective (by rw [hm]; exact h1))
  intro p b
  rw [← hm]
  exact map_supportedOn i (fun _ h => h) (hy p b)

lemma positive_unit_flow_chain {c : Chains E} (hg : c ∈ grade 2) (hp : Positive c)
    (s t : E) (hb : boundary c = bracket [t] - bracket [s]) :
    ∃ S : Set E, S.Finite ∧ (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
      s ∈ S ∧ t ∈ S ∧ (∀ a ∈ S, s ≤ a ∧ a ≤ t) ∧ c ∈ supportedOn S := by
  classical
  generalize hm : (chainMass c).toNat = m
  induction m using Nat.strong_induction_on generalizing c s t with
  | h m ih =>
    by_cases hst : s = t
    · subst t
      have hz : c = 0 := positive_cycle_zero_partial hg hp (by simpa using hb)
      refine ⟨{s}, Set.finite_singleton s, ?_, by simp, by simp, ?_, ?_⟩
      · intro a ha b hb
        simp only [Set.mem_singleton_iff] at ha hb
        subst a; subst b; exact Or.inl le_rfl
      · intro a ha
        simp only [Set.mem_singleton_iff] at ha
        subst a; exact ⟨le_rfl, le_rfl⟩
      · rw [hz]; exact (supportedOn _).zero_mem
    · obtain ⟨b, hsb, hpos⟩ := positive_unit_flow_outgoing hg hp hst hb
      let w : Word E := ⟨[s,b], by simpa using hsb⟩
      let d := c - bracket w.val
      have hdg : d ∈ grade 2 := (grade 2).sub_mem hg (bracket_mem_grade [s,b])
      have hdp : Positive d := positive_peel hp w hpos
      have hdb : boundary d = bracket [t] - bracket [b] := by
        dsimp only [d]
        rw [map_sub, hb, boundary_bracket (w.property.imp le_of_lt), wordBoundary_pair]
        abel
      have hmass : chainMass d = chainMass c - 1 := by rw [map_sub, chainMass_bracket]
      have hlt : (chainMass d).toNat < m := by
        rw [← hm, Int.toNat_lt_toNat (chainMass_pos hp hpos), hmass]
        omega
      obtain ⟨S, hSf, hSc, hbS, htS, hSbounds, hdS⟩ := ih _ hlt hdg hdp b t hdb rfl
      have hsle : ∀ a ∈ S, s ≤ a := fun a ha => hsb.le.trans (hSbounds a ha).1
      refine ⟨insert s S, hSf.insert s, ?_, Set.mem_insert s S, Set.mem_insert_of_mem s htS, ?_, ?_⟩
      · intro a ha b hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact Or.inl le_rfl
          · exact Or.inl (hsle b hb)
        · rcases hb with rfl | hb
          · exact Or.inr (hsle a ha)
          · exact hSc a ha b hb
      · intro a ha
        rcases ha with rfl | ha
        · exact ⟨le_rfl, hsle t htS⟩
        · exact ⟨hsle a ha, (hSbounds a ha).2⟩
      · have he : c = d + bracket [s,b] := by dsimp [d,w]; abel
        rw [he]
        apply (supportedOn _).add_mem
        · exact supportedOn_mono (Set.subset_insert s S) hdS
        · apply bracket_mem_supportedOn
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with ha | ha
          · subst a; exact Set.mem_insert s S
          · subst a; exact Set.mem_insert_of_mem s hbS

lemma table_finite_chain_support (x : Table (complex E)) :
    ∃ S : Set E, S.Finite ∧ (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
      (∀ p b, (x.row p b).val ∈ supportedOn S) := by
  obtain ⟨s, hs⟩ := table_zero_row_vertex x false
  obtain ⟨t, ht⟩ := table_zero_row_vertex x true
  have hb : boundary (x.row 1 true).val = bracket [t] - bracket [s] := by
    have he := congrArg Subtype.val (x.boundary 0 true)
    change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
    simpa [hs, ht] using he
  obtain ⟨S, hSf, hSc, hsS, htS, hbounds, h1⟩ :=
    positive_unit_flow_chain (x.row 1 true).property (x.positive 1 true) s t hb
  refine ⟨S,hSf,hSc, table_support_of_target S x ?_ h1⟩
  rw [hs]
  exact (vertex_supportedOn_iff s S).mpr hsS

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex DirectedComplex.Table
variable {E : Type u} [PartialOrder E]

lemma table_truncate_supported (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) (k : ℕ) (e : Bool) :
    ∀ p b, ((truncate k e x).row p b).val ∈ supportedOn S := by
  intro p b
  simp only [truncate_row]
  split_ifs
  · exact hx p b
  · exact hx p e
  · exact (supportedOn S).zero_mem

lemma table_comp_supported_factors (S : Set E) (k : ℕ) (x y : Table (complex E))
    (h : truncate k true x = truncate k false y)
    (hz : ∀ p b, ((comp k x y h).row p b).val ∈ supportedOn S) :
    (∀ p b, (x.row p b).val ∈ supportedOn S) ∧
      (∀ p b, (y.row p b).val ∈ supportedOn S) := by
  have h0 := hz 0 false
  have h1 := hz 1 true
  have h0x : (x.row 0 false).val ∈ supportedOn S := by
    cases k with
    | zero => exact h0
    | succ k => simpa only [comp_row, Nat.zero_lt_succ, ite_true] using h0
  have h1y : (y.row 1 true).val ∈ supportedOn S := by
    cases k with
    | zero => exact (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) h1).2
    | succ k =>
      cases k with
      | zero => simpa using h1
      | succ k =>
        have he := lower_rows_eq h (show 1 < k+1+1 by omega) true
        simpa [show 1 < k+1+1 by omega, he] using h1
  cases k with
  | zero =>
    have h1x : (x.row 1 true).val ∈ supportedOn S :=
      (supportedOn_of_add_positive (x.positive 1 true) (y.positive 1 true) h1).1
    have h0y : (y.row 0 false).val ∈ supportedOn S := by
      rw [← matching_row_eq h]
      exact table_finish_supported x h0x h1x
    exact ⟨table_support_of_target S x h0x h1x, table_support_of_target S y h0y h1y⟩
  | succ k =>
    have h0y : (y.row 0 false).val ∈ supportedOn S := by
      rw [← lower_rows_eq h (Nat.zero_lt_succ k) false]
      exact h0x
    have hy' := table_support_of_target S y h0y h1y
    have h1x : (x.row 1 true).val ∈ supportedOn S := by
      cases k with
      | zero => rw [matching_row_eq h]; exact hy' 1 false
      | succ k =>
        rw [lower_rows_eq h (show 1 < k+1+1 by omega) true]
        exact h1y
    exact ⟨table_support_of_target S x h0x h1x, hy'⟩

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteChains
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Chains. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory NormalizedChains OmegaCategory DirectedComplex
variable {P : Type u} [PartialOrder P]

namespace FiniteVertexChain
variable (S : FiniteVertexChain P)

abbrev Supports (x : Table (complex P)) : Prop :=
  ∀ p b, (x.row p b).val ∈ supportedOn S.vertices

lemma supports_inter (T : FiniteVertexChain P) (x : Table (complex P))
    (hS : S.Supports x) (hT : T.Supports x) : (S.inter T).Supports x := by
  intro p b
  rw [mem_supportedOn_iff]
  intro w hw a ha
  exact ⟨(mem_supportedOn_iff _ _).mp (hS p b) w hw a ha,
    (mem_supportedOn_iff _ _).mp (hT p b) w hw a ha⟩

noncomputable instance tableMap_isIso : IsIso (posetCategorificationTableMap S.vertices) := by
  let := S.linearOrder
  exact posetCategorificationTableMap_finiteLinear_isIso_all S.vertices

noncomputable def lift : (complex S.vertices).nu ⟶ categorification.obj (nerve P) :=
  inv (posetCategorificationTableMap S.vertices) ≫
    categorification.map (CategoryTheory.nerveMap S.inclusion.monotone.functor)

lemma lift_comp_tableMap : S.lift ≫ posetCategorificationTableMap P = (complexMap S.inclusion).nu := by
  unfold lift
  rw [Category.assoc, posetCategorificationTableMap_natural, IsIso.inv_hom_id_assoc]

lemma lift_natural (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices) :
    (complexMap (S.subInclusion T h)).nu ≫ T.lift = S.lift := by
  apply (cancel_epi (posetCategorificationTableMap S.vertices)).mp
  rw [← Category.assoc, ← posetCategorificationTableMap_natural, lift, Category.assoc,
    IsIso.hom_inv_id_assoc]
  unfold lift
  rw [IsIso.hom_inv_id_assoc, ← categorification.map_comp]
  congr 1

lemma table_subInclusion_restrict (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices)
    (x : Table (complex P)) (hxS : S.Supports x) (hxT : T.Supports x) :
    (complexMap (S.subInclusion T h)).table (restrictTable S.vertices x hxS) =
      restrictTable T.vertices x hxT := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype T.vertices)
  have hcomp : T.inclusion.comp (S.subInclusion T h) = S.inclusion := rfl
  change (DirectedComplex.Hom.comp (complexMap (S.subInclusion T h))
    (complexMap T.inclusion)).table _ = (complexMap T.inclusion).table _
  rw [← complexMap_comp, hcomp, table_map_restrictTable, table_map_restrictTable]

noncomputable def liftAt (x : Table (complex P)) (hx : S.Supports x) :
    (categorification.obj (nerve P)).Cell := S.lift.map (restrictTable S.vertices x hx)

lemma liftAt_natural (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices)
    (x : Table (complex P)) (hxS : S.Supports x) (hxT : T.Supports x) :
    S.liftAt x hxS = T.liftAt x hxT := by
  have he := congrArg (fun F => F.map (restrictTable S.vertices x hxS)) (S.lift_natural T h)
  change T.lift.map ((complexMap (S.subInclusion T h)).table _) = S.liftAt x hxS at he
  rw [S.table_subInclusion_restrict T h x hxS hxT] at he
  exact he.symm

lemma liftAt_independent (T : FiniteVertexChain P) (x : Table (complex P))
    (hxS : S.Supports x) (hxT : T.Supports x) : S.liftAt x hxS = T.liftAt x hxT := by
  have hU := S.supports_inter T x hxS hxT
  exact ((S.inter T).liftAt_natural S Set.inter_subset_left x hU hxS).symm.trans
    ((S.inter T).liftAt_natural T Set.inter_subset_right x hU hxT)

lemma liftAt_table (x : Table (complex P)) (hx : S.Supports x) :
    (posetCategorificationTableMap P).map (S.liftAt x hx) = x := by
  have he := congrArg (fun F => F.map (restrictTable S.vertices x hx)) S.lift_comp_tableMap
  exact he.trans (table_map_restrictTable S.vertices x hx)

lemma restrict_truncate (x : Table (complex P)) (hx : S.Supports x) (k : ℕ) (e : Bool)
    (ht : S.Supports (Table.truncate k e x)) :
    restrictTable S.vertices (Table.truncate k e x) ht =
      Table.truncate k e (restrictTable S.vertices x hx) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [table_map_restrictTable, DirectedComplex.Hom.table_truncate, table_map_restrictTable]

lemma restrict_composable (k : ℕ) (x y : Table (complex P))
    (h : Table.truncate k true x = Table.truncate k false y)
    (hx : S.Supports x) (hy : S.Supports y) :
    Table.truncate k true (restrictTable S.vertices x hx) =
      Table.truncate k false (restrictTable S.vertices y hy) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [DirectedComplex.Hom.table_truncate, DirectedComplex.Hom.table_truncate,
    table_map_restrictTable, table_map_restrictTable, h]

lemma restrict_comp (k : ℕ) (x y : Table (complex P))
    (h : Table.truncate k true x = Table.truncate k false y)
    (hx : S.Supports x) (hy : S.Supports y) (hz : S.Supports (Table.comp k x y h)) :
    restrictTable S.vertices (Table.comp k x y h) hz =
      Table.comp k (restrictTable S.vertices x hx) (restrictTable S.vertices y hy)
        (S.restrict_composable k x y h hx hy) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [table_map_restrictTable]
  have he := (complexMap S.inclusion).table_comp k _ _
    (S.restrict_composable k x y h hx hy) (by
      rw [table_map_restrictTable, table_map_restrictTable]; exact h)
  dsimp only [inclusion] at he
  apply Eq.trans ?_ he.symm
  ext p b
  simp only [Table.comp_row]
  rw [table_map_restrictTable S.vertices x hx, table_map_restrictTable S.vertices y hy]

end FiniteVertexChain

noncomputable def tableChainSupport (x : Table (complex P)) : FiniteVertexChain P :=
  let h := table_finite_chain_support x
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩

lemma tableChainSupport_supports (x : Table (complex P)) : (tableChainSupport x).Supports x :=
  (table_finite_chain_support x).choose_spec.2.2

noncomputable def posetTableInverseMap (x : Table (complex P)) :
    (categorification.obj (nerve P)).Cell :=
  (tableChainSupport x).liftAt x (tableChainSupport_supports x)

lemma posetTableInverseMap_eq (S : FiniteVertexChain P) (x : Table (complex P)) (hx : S.Supports x) :
    posetTableInverseMap x = S.liftAt x hx :=
  (tableChainSupport x).liftAt_independent S x (tableChainSupport_supports x) hx

noncomputable def posetTableInverse (P : Type u) [PartialOrder P] :
    (complex P).nu ⟶ categorification.obj (nerve P) where
  map := posetTableInverseMap
  map_source k x := by
    let S := tableChainSupport x
    have hx : S.Supports x := tableChainSupport_supports x
    have ht : S.Supports (Table.truncate k false x) := table_truncate_supported S.vertices x hx k false
    change posetTableInverseMap (Table.truncate k false x) = _
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S _ ht]
    unfold FiniteVertexChain.liftAt
    rw [S.restrict_truncate x hx k false ht]
    exact S.lift.map_source k _
  map_target k x := by
    let S := tableChainSupport x
    have hx : S.Supports x := tableChainSupport_supports x
    have ht : S.Supports (Table.truncate k true x) := table_truncate_supported S.vertices x hx k true
    change posetTableInverseMap (Table.truncate k true x) = _
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S _ ht]
    unfold FiniteVertexChain.liftAt
    rw [S.restrict_truncate x hx k true ht]
    exact S.lift.map_target k _
  map_comp k x y h h' := by
    let S := tableChainSupport (Table.comp k x y h)
    have hz : S.Supports (Table.comp k x y h) := tableChainSupport_supports _
    obtain ⟨hx,hy⟩ := table_comp_supported_factors S.vertices k x y h hz
    change posetTableInverseMap (Table.comp k x y h) = _
    revert h'
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S y hy,
      posetTableInverseMap_eq S _ hz]
    intro h'
    unfold FiniteVertexChain.liftAt at h' ⊢
    rw [S.restrict_comp k x y h hx hy hz]
    exact S.lift.map_comp k _ _ (S.restrict_composable k x y h hx hy) h'

lemma posetTableInverse_comp_tableMap (P : Type u) [PartialOrder P] :
    posetTableInverse P ≫ posetCategorificationTableMap P = 𝟙 _ := by
  apply OmegaCategory.Functor.ext
  funext x
  exact (tableChainSupport x).liftAt_table x (tableChainSupport_supports x)

lemma posetTableInverse_on_chain (S : FiniteVertexChain P) :
    (complexMap S.inclusion).nu ≫ posetTableInverse P = S.lift := by
  apply OmegaCategory.Functor.ext
  funext x
  have hx : S.Supports ((complexMap S.inclusion).table x) := by
    intro p b
    exact map_mem_supportedOn S.vertices (x.row p b).val
  change posetTableInverseMap ((complexMap S.inclusion).table x) = S.lift.map x
  rw [posetTableInverseMap_eq S _ hx]
  unfold FiniteVertexChain.liftAt
  congr 1
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  exact table_map_restrictTable S.vertices _ hx

attribute [local instance] posetCategorificationTableMap_finiteLinear_isIso_all

lemma posetTableInverse_finite_natural {Q : Type u} [LinearOrder Q] [Finite Q]
    (f : Q →o P) :
    (complexMap f).nu ≫ posetTableInverse P =
      inv (posetCategorificationTableMap Q) ≫
        categorification.map (CategoryTheory.nerveMap f.monotone.functor) := by
  let S := finiteRangeChain f
  let g := finiteRangeFactor f
  have hf : S.inclusion.comp g = f := rfl
  rw [← hf, complexMap_comp]
  change ((complexMap g).nu : (complex Q).nu ⟶ (complex S.vertices).nu) ≫
    ((complexMap S.inclusion).nu ≫ posetTableInverse P) = _
  rw [posetTableInverse_on_chain]
  apply (cancel_epi (posetCategorificationTableMap Q)).mp
  rw [← Category.assoc, ← posetCategorificationTableMap_natural]
  unfold FiniteVertexChain.lift
  rw [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc,
    ← categorification.map_comp]
  rfl

lemma posetCategorificationTableMap_comp_inverse (P : Type u) [PartialOrder P] :
    posetCategorificationTableMap P ≫ posetTableInverse P = 𝟙 _ := by
  apply (posetSimplexIsColimit P).hom_ext
  intro s
  change categorification.map (CategoryTheory.nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (posetCategorificationTableMap P ≫ posetTableInverse P) =
    categorification.map (CategoryTheory.nerveMap (simplexVertexOrder s).monotone.functor) ≫ 𝟙 _
  rw [← Category.assoc, posetCategorificationTableMap_natural, Category.assoc,
    posetTableInverse_finite_natural]
  rw [IsIso.hom_inv_id_assoc, Category.comp_id]

noncomputable instance posetCategorificationTableMap_isIso (P : Type u) [PartialOrder P] :
    IsIso (posetCategorificationTableMap P) :=
  ⟨⟨posetTableInverse P, posetCategorificationTableMap_comp_inverse P,
    posetTableInverse_comp_tableMap P⟩⟩

end Thomason

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

namespace Thomason.OmegaCategory
open CategoryTheory Limits

theorem endpoint_attachment {C X Y : OmegaCategory.{u}} (q : C ⟶ interval) (e : Fin 2)
    (a : (q.fiber (intervalVertex e)).category ⟶ X) (h : X ⟶ Y) (i : C ⟶ Y)
    (H : IsPushout a (q.fiber (intervalVertex e)).inclusion h i) :
    ∃ (η : Y ⟶ interval) (E : X ≅ (η.fiber (intervalVertex e)).category),
      E.hom ≫ (η.fiber (intervalVertex e)).inclusion = h := by
  let A := (q.fiber (intervalVertex e)).category
  let η : Y ⟶ interval := H.desc (constantLabel X e) q
    ((comp_constantLabel a e).trans (fiberInclusion_label q e).symm)
  have hh : h ≫ η = constantLabel X e := H.inl_desc _ _ _
  have hi : i ≫ η = q := H.inr_desc _ _ _
  let af : Over.mk (constantLabel A e) ⟶ Over.mk (constantLabel X e) :=
    Over.homMk a (comp_constantLabel a e)
  let gf : Over.mk (constantLabel A e) ⟶ Over.mk q :=
    Over.homMk (q.fiber (intervalVertex e)).inclusion (fiberInclusion_label q e)
  let hf : Over.mk (constantLabel X e) ⟶ Over.mk η := Over.homMk h hh
  let iF : Over.mk q ⟶ Over.mk η := Over.homMk i hi
  let F := fiberFunctor (intervalVertex e)
  have hp := labelled_pushout_fibers af gf hf iF H e
  let : IsIso (F.map gf) := (isoOfBijective (F.map gf) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hxy
    · intro x
      exact ⟨⟨x,rfl⟩,rfl⟩)).isIso_hom
  let : IsIso (F.map hf) := hp.isIso_inl_of_isIso
  let fiberIso := asIso (F.map hf)
  let E : X ≅ (η.fiber (intervalVertex e)).category :=
    constantFiberIso X e ≪≫ fiberIso
  refine ⟨η,E,?_⟩
  rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory

def posetPieceFiberIso {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    categorification.obj (nerve S) ≅
      ((posetCategorificationLabel l).fiber (intervalVertex e)).category := by
  subst S
  exact posetCategorificationFiberIso l e

lemma posetPieceFiberIso_inclusion {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (posetPieceFiberIso S l e hS).hom ≫
        ((posetCategorificationLabel l).fiber (intervalVertex e)).inclusion =
      categorification.map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) := by
  subst S
  exact posetCategorificationFiberMap_inclusion l e

theorem poset_sieve_attachment {P : Type u} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) {X Y : OmegaCategory.{u}}
    (a : categorification.obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ S : Set Y.Objects, Y.IsObjectSieve S ∧
      ∃ e : X ≅ (Y.fullOn S).category, e.hom ≫ (Y.fullOn S).inclusion = h := by
  let l := NormalizedChains.PosetTables.lowerSegmentLabel A hA
  have hA' : A = {p | l p = 0} := by
    ext p
    exact (NormalizedChains.PosetTables.lowerSegmentLabel_zero A hA p).symm
  let E := posetPieceFiberIso A l 0 hA'
  have hp : IsPushout (E.inv ≫ a)
      ((posetCategorificationLabel l).fiber (intervalVertex 0)).inclusion h i :=
    H.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id]; exact (posetPieceFiberIso_inclusion A l 0 hA').symm)
      (by simp) (by simp)
  obtain ⟨η,F,hF⟩ := endpoint_attachment (posetCategorificationLabel l) 0 (E.inv ≫ a) h i hp
  refine ⟨intervalFiberObjects η 0, zero_fiber_isObjectSieve η,
    F ≪≫ intervalFiberFullIso η 0, ?_⟩
  exact hF

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

def IsPosetAttachmentPiece {P : Type u} [PartialOrder P]
    (A S : Set P) (hAS : A ⊆ S) {X Y : OmegaCategory.{u}}
    (a : categorification.obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : categorification.obj (nerve P) ⟶ Y) (T : Set Y.Objects) : Prop :=
  ∃ (j : X ⟶ (Y.fullOn T).category)
    (k : categorification.obj (nerve S) ⟶ (Y.fullOn T).category),
    j ≫ (Y.fullOn T).inclusion = h ∧
    k ≫ (Y.fullOn T).inclusion = categorification.map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i ∧
    IsPushout a (categorification.map (nerveMap (subposetMap A S hAS).monotone.functor)) j k

def IsPosetNewPiece {P : Type u} [PartialOrder P]
    (S : Set P) {Y : OmegaCategory.{u}}
    (i : categorification.obj (nerve P) ⟶ Y) (T : Set Y.Objects) : Prop :=
  ∃ e : categorification.obj (nerve S) ≅ (Y.fullOn T).category,
    e.hom ≫ (Y.fullOn T).inclusion = categorification.map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i

open NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

lemma subposetMap_comp (S : Set P) (hAS : A ⊆ S) :
    categorification.map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
      categorification.map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) =
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor) := by
  rw [← categorification.map_comp]
  rfl

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma maxLabel_objects_fiber {C : OmegaCategory.{u}} (p q : C ⟶ interval) :
    intervalFiberObjects (maxLabel p q) 0 =
      intervalFiberObjects p 0 ∩ intervalFiberObjects q 0 := by
  ext x
  change (maxLabel p q).objects x = intervalVertex 0 ↔
    p.objects x = intervalVertex 0 ∧ q.objects x = intervalVertex 0
  erw [← Subtype.val_inj,← Subtype.val_inj,← Subtype.val_inj]
  exact Set.ext_iff.mp (maxLabel_zero_fiber p q) x.val

lemma comp_maxLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (p q : D ⟶ interval) :
    f ≫ maxLabel p q = maxLabel (f ≫ p) (f ≫ q) := rfl
lemma comp_minLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (p q : D ⟶ interval) :
    f ≫ minLabel p q = minLabel (f ≫ p) (f ≫ q) := rfl

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

lemma posetFiniteLabel_max (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l₁ l₂ : P →o Fin 2) :
    posetCategorificationFiniteLabel n hn
      (⟨fun p => max (l₁ p) (l₂ p),fun _ _ he => max_le_max (l₁.monotone he) (l₂.monotone he)⟩ : P →o Fin 2) =
      maxLabel (posetCategorificationFiniteLabel n hn l₁) (posetCategorificationFiniteLabel n hn l₂) := by
  apply truncation_functor_ext
  rfl

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables
def maxFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) : C ⟶ finiteInterval n hn := maxLabel p q

lemma comp_maxFiniteLabel (n : ℕ) (hn : 1 ≤ n) {C D : NCategory.{u} n}
    (f : C ⟶ D) (p q : D ⟶ finiteInterval n hn) :
    f ≫ maxFiniteLabel n hn p q = maxFiniteLabel n hn (f ≫ p) (f ≫ q) := rfl

lemma maxFiniteLabel_objects_fiber (n : ℕ) (hn : 1 ≤ n) {C : NCategory.{u} n}
    (p q : C ⟶ finiteInterval n hn) :
    intervalFiberObjects (maxFiniteLabel n hn p q) 0 = intervalFiberObjects p 0 ∩ intervalFiberObjects q 0 :=
  maxLabel_objects_fiber p q

end Thomason.Attachments

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
open CategoryTheory Limits

namespace Thomason.OmegaCategory

lemma comp_of_right_source_fixed (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y) (hy : C.source k y = y) :
    C.comp k x y h = x := by
  have hy' : y = C.target k x := (h.trans hy).symm
  subst y
  exact C.unit_right k x h

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RecursiveCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

def shiftDown (n p : ℕ) : Chain.{u} (n+1) (p+1) ≃ₗ[ℤ] Chain.{u} n p where
  toFun x := ⟨x.val, by
    intro b hb
    apply x.property b
    rcases hb with h | ⟨h, hb⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hb⟩⟩
  invFun x := ⟨x.val, by
    intro b hb
    apply x.property b
    rcases hb with h | ⟨h, hb⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hb⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma shiftDown_coordinate (n p : ℕ) (x : Chain.{u} (n+1) (p+1))
    (i : ULift.{u} Bool) : (shiftDown n p x).val i = x.val i := rfl

@[simp] lemma shiftUp_coordinate (n p : ℕ) (x : Chain.{u} n p) (i : ULift.{u} Bool) :
    ((shiftDown n p).symm x).val i = x.val i := rfl

@[simp] lemma mass_shiftDown (n p : ℕ) (x : Chain.{u} (n+1) (p+1)) :
    mass n p (shiftDown n p x) = mass (n+1) (p+1) x := rfl

@[simp] lemma mass_shiftUp (n p : ℕ) (x : Chain.{u} n p) :
    mass (n+1) (p+1) ((shiftDown n p).symm x) = mass n p x := rfl

end Thomason.GlobeComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GreatestAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greatest Attachments. -/

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u})

lemma finite_nerve_weak_of_zigzag {n : ℕ} {X Y : NCategory.{u} n}
    (j : X ⟶ Y) (p : Y ⟶ X) (H : Y ⟶ Y) (hp : j ≫ p = 𝟙 X)
    (h₀ : SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y)) ((streetNerveFinite n).map H))
    (h₁ : SSet.Homotopy ((streetNerveFinite n).map (p ≫ j)) ((streetNerveFinite n).map H)) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  have hH : simplicialWeakEquivalences ((streetNerveFinite n).map H) :=
    (simplicialWeakEquivalences_homotopy h₀).mp (simplicialWeakEquivalences.id_mem _)
  have hw : simplicialWeakEquivalences ((streetNerveFinite n).map (p ≫ j)) :=
    (simplicialWeakEquivalences_homotopy h₁).mpr hH
  have rt : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc,hp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by ext <;> simp [hp] }
  exact simplicialWeakEquivalences.of_retract (rt.map (streetNerveFinite n)) hw

end Thomason.RightIntervalExtension

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Couniversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Couniversality. -/

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma finite_nerve_upper_mono (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P) (hS : IsUpperSet S) :
    Mono ((streetNerveFinite n).map (inc n S)) := by
  let l := NormalizedChains.PosetTables.upperSegmentLabel S hS
  have hS' : S = {p | l p = 1} := by
    ext p
    exact (NormalizedChains.PosetTables.upperSegmentLabel_one S hS p).symm
  let e := posetPieceFiniteFiberIso n hn S l 1 hS'
  have he := posetPieceFiniteFiberIso_inclusion n hn S l 1 hS'
  have := fiberFiniteInclusion_mono n hn 1
    (Over.mk (posetCategorificationFiniteLabel n hn l))
  have : Mono (inc n S) := by
    change Mono ((categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ S)).toOrderHom.monotone.functor))
    rw [← he]
    infer_instance
  let : PreservesLimits (streetNerveFinite n) :=
    (categorificationFiniteAdjunction n).rightAdjoint_preservesLimits
  infer_instance

lemma finite_nerve_inter_upper_mono (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (Z C : Set P) (hZ : IsUpperSet Z) :
    Mono ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right)) := by
  let e := nestedOldIso (categorificationFinite n) (Z ∩ C) C Set.inter_subset_right
  have : Mono ((streetNerveFinite n).map (inc n {c : C | c.val ∈ Z ∩ C})) :=
    finite_nerve_upper_mono n hn _ (by
      intro x y hxy hx
      exact ⟨hZ hxy hx.1,y.property⟩)
  have he : sb n (Z ∩ C) C Set.inter_subset_right =
      e.inv ≫ inc n {c : C | c.val ∈ Z ∩ C} := by
    calc
      _ = e.inv ≫ (e.hom ≫ sb n (Z ∩ C) C Set.inter_subset_right) := by simp
      _ = _ := congrArg (e.inv ≫ ·) (nestedOldIso_inc
        (categorificationFinite n) (Z ∩ C) C Set.inter_subset_right)
  rw [he, CategoryTheory.Functor.map_comp]
  infer_instance

end Thomason.AttachmentComparison

end

end OAI
end


