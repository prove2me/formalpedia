-- Prove2me | Definitions.Def_OAIQ043T006
-- name    : OAIQ043T006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:54:10.37349+00:00
-- url     : https://prove2.me/theorems/5e18d42a-6cee-4af2-bd67-803c4a9a2efc
-- title:
--   Definitions bundle OAIQ043T006 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 114 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure, 1 instance and 84 theorems. The definitions and types are `OAI.Thomason.Attachments.constantAttachmentLabel`, `OAI.Thomason.GlobeComplex.evaluate`, `OAI.Thomason.GlobeComplex.faceMap`, `OAI.Thomason.GlobeComplex.lift`, `OAI.Thomason.GlobeComplex.sourceCollapse`, `OAI.Thomason.GlobeComplex.suspendTable`, `OAI.Thomason.GlobeComplex.tableMap`, `OAI.Thomason.GlobeComplex.tableRowMap`, `OAI.Thomason.GlobeComplex.vertexWeights`, `OAI.Thomason.GrayRecursive.IsDiagonal`, `OAI.Thomason.GrayRecursive.K`, `OAI.Thomason.GrayRecursive.atEnd`, `OAI.Thomason.GrayRecursive.corner`, `OAI.Thomason.GrayRecursive.crossRow`, `OAI.Thomason.GrayRecursive.diagonalRow`, `OAI.Thomason.GrayRecursive.down`, `OAI.Thomason.GrayRecursive.downRow`, `OAI.Thomason.GrayRecursive.project`, `OAI.Thomason.GrayRecursive.sideRow`, `OAI.Thomason.GrayRecursive.up`, `OAI.Thomason.GrayRecursive.upRow`, `OAI.Thomason.GrayRecursive.vertex`, `OAI.Thomason.RelativePrismData.finiteAntihomotopy`, `OAI.Thomason.RelativePrismData.finiteCylinderChainMap`, `OAI.Thomason.RelativePrismData.prism`, `OAI.Thomason.RelativePrismData.prismCocone`, `OAI.Thomason.RelativePrismData.prismLeg`, `OAI.Thomason.RightIntervalExtension`, `OAI.Thomason.RightIntervalExtension.cut`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_AttachmentComparison`, `Thomason_Couniversality`, `Thomason_DimensionOne`, `Thomason_FiniteAttachments`, `Thomason_GlobularComplexes`, `Thomason_GlobularGeneration`, `Thomason_GrayGenerators`, `Thomason_GreatestAttachments`, `Thomason_IntervalExtension`, `Thomason_Linearization`, `Thomason_PartialPrisms`, `Thomason_RecursiveCylinders`, `Thomason_SieveAttachments`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T004` and `OAIQ043T005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T008` and `OAIQ043T009`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T004
import Definitions.Def_OAIQ043T005

section
-- module Solutions.OAIQ043_TH.Thomason_Linearization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.FiniteVertexChain.tableMap_isIso _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.NormalizedChains.finiteTables _root_.OAI.Thomason.OmegaCategory.FilteredColimit.globeHomPreservesColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.nInclusion_preservesFilteredColimit _root_.OAI.Thomason.OmegaCategory.FilteredColimit.streetPreservesColimit _root_.OAI.Thomason.OmegaCategory.globe_finitelyPresentable _root_.OAI.Thomason.OmegaCategory.locallyFinitelyPresentable _root_.OAI.Thomason.OmegaCategory.locallyPresentable _root_.OAI.Thomason.OmegaCategory.nInclusion_finitelyAccessible _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.orientalFiniteCells _root_.OAI.Thomason.posetCategorificationTableMap_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.streetPreservesFilteredShape _root_.OAI.Thomason.street_preservesFilteredColimits _root_.OAI.Thomason.thomasonBoundary_smallCardinal _root_.OAI.Thomason.thomasonHorn_smallCardinal _root_.OAI.Thomason.thomasonLeft_finitelyPresentable _root_.OAI.Thomason.thomasonRight_finitelyAccessible _root_.OAI.Thomason.thomasonRight_preservesFilteredColimits _root_.OAI.Thomason.thomasonWeakEquivalences_hasTwoOutOfThreeProperty _root_.OAI.Thomason.thomasonWeakEquivalences_isStableUnderRetracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearization. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

instance fullOnMap_nerve_mono {C : OmegaCategory.{u}} {S T : Set C.Objects} (h : S ⊆ T) :
    Mono (streetNerveMap (fullOnMap h)) := by
  exact mono_of_mono_fac (show streetNerveMap (fullOnMap h) ≫ streetNerveMap (C.fullOn T).inclusion =
    streetNerveMap (C.fullOn S).inclusion from rfl)

lemma fullNerve_sieve_sup {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    C.fullNerve S ⊔ C.fullNerve T = ⊤ := by
  apply top_unique
  intro n F _
  rcases hcover (F.objects (NormalizedChains.tableObjectsEquiv.symm
      (Fin.last n.unop.len))) with h | h
  · exact Or.inl (simplex_objects_mem_sieve F hS h)
  · exact Or.inr (simplex_objects_mem_sieve F hT h)

lemma sieve_cover_nerve_isPushout {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hcover : ∀ a : C.Objects, a ∈ S ∨ a ∈ T) :
    IsPushout (streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T))))
      (streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T))))
      (streetNerveMap (C.fullOn S).inclusion) (streetNerveMap (C.fullOn T).inclusion) :=
  fullNerve_isPushout (fullNerve_sieve_sup hS hT hcover)

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularComplexes
attribute [-instance] _root_.OAI.Thomason.FiniteVertexChain.tableMap_isIso _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces _root_.OAI.Thomason.OmegaCategory.oneSkeletonCategory _root_.OAI.Thomason.Subdivision.ex_preservesFilteredColimits _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.finiteOrderNerve _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits _root_.OAI.Thomason.categorificationSimplexLeg_isIso _root_.OAI.Thomason.finiteInclusion_preservesFilteredColimits _root_.OAI.Thomason.posetCategorificationTableMap_isIso _root_.OAI.Thomason.posetCategorificationTableMap_ordinal_isIso _root_.OAI.Thomason.street_preservesFilteredColimits _root_.OAI.Thomason.thomasonBoundary_smallCardinal _root_.OAI.Thomason.thomasonHorn_smallCardinal _root_.OAI.Thomason.thomasonLeft_finitelyPresentable _root_.OAI.Thomason.thomasonRight_finitelyAccessible _root_.OAI.Thomason.thomasonRight_preservesFilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma face_face (C : OmegaCategory.{u}) (p q : ℕ) (a b : Bool) (x : C.Cell) :
    C.face p a (C.face q b x) = if p < q then C.face p a x else C.face q b x := by
  cases a <;> cases b <;>
    simp only [face, Bool.false_eq_true, ite_false, ite_true]
  · rw [C.source_source]
    split_ifs with h
    · rw [min_eq_left (Nat.le_of_lt h)]
    · rw [min_eq_right (Nat.le_of_not_gt h)]
  · exact C.source_target p q x
  · exact C.target_source p q x
  · rw [C.target_target]
    split_ifs with h
    · rw [min_eq_left (Nat.le_of_lt h)]
    · rw [min_eq_right (Nat.le_of_not_gt h)]

lemma face_of_fixed (C : OmegaCategory.{u}) {n p : ℕ} {x : C.Cell}
    (hx : C.source n x = x) (hnp : n ≤ p) (b : Bool) : C.face p b x = x := by
  cases b
  · exact C.source_fixed_upwards hnp hx
  · exact C.target_eq_self_of_source_eq_self (C.source_fixed_upwards hnp hx)

lemma Functor.map_face {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (p : ℕ) (b : Bool) (x : C.Cell) :
    F.map (C.face p b x) = D.face p b (F.map x) := by
  cases b
  · exact F.map_source p x
  · exact F.map_target p x

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex DirectedComplex.Table OmegaCategory

lemma face_nu (n p : ℕ) (b : Bool) (x : Table (complex.{u} n)) :
    (complex n).nu.face p b x = truncate p b x := by cases b <;> rfl

lemma face_evaluation_well_defined {n p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (a b : Bool) (h : truncate p a (topTable.{u} n) = truncate q b (topTable n))
    {C : OmegaCategory.{v}} (x : C.Cell) (hx : C.source n x = x) :
    C.face p a x = C.face q b x := by
  have he := top_face_dimension hp hq a b h
  subst q
  by_cases hp' : p < n
  · rw [top_face_sign hp' a b h]
  · have hn : n ≤ p := by omega
    rw [C.face_of_fixed hx hn, C.face_of_fixed hx hn]

noncomputable def evaluate {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (t : Table (complex.{u} n)) : C.Cell :=
  let p := (table_classification t).choose
  let b := (table_classification t).choose_spec.choose
  C.face p b x

lemma evaluate_face {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) (p : ℕ) (b : Bool) :
    evaluate x (truncate p b (topTable.{u} n)) = C.face p b x := by
  by_cases hp : p ≤ n
  · let t := truncate p b (topTable.{u} n)
    obtain ⟨hqn, ht⟩ := (table_classification t).choose_spec.choose_spec
    exact face_evaluation_well_defined hqn hp _ b ht.symm x hx
  · have hnp : n ≤ p := by omega
    have he : truncate p b (topTable.{u} n) = topTable n :=
      (face_nu n p b (topTable n)).symm.trans
        ((complex n).nu.face_of_fixed (topTable_bounded n) hnp b)
    rw [he, C.face_of_fixed hx hnp]
    obtain ⟨hqn, ht⟩ := (table_classification (topTable.{u} n)).choose_spec.choose_spec
    exact (face_evaluation_well_defined hqn (le_refl n) _ false
      (ht.symm.trans (topTable_bounded n).symm) x hx).trans hx

lemma evaluate_top {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : evaluate x (topTable.{u} n) = x := by
  rw [← topTable_bounded n, evaluate_face x hx]
  exact hx

lemma evaluate_truncate {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) (t : Table (complex.{u} n)) (k : ℕ) (a : Bool) :
    evaluate x (truncate k a t) = C.face k a (evaluate x t) := by
  obtain ⟨p, b, _, rfl⟩ := table_classification t
  rw [truncate_truncate, evaluate_face x hx, C.face_face]
  split_ifs <;> rw [evaluate_face x hx]

noncomputable def lift {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : OmegaCategory.Functor (complex.{u} n).nu C where
  map := evaluate x
  map_source k t := evaluate_truncate x hx t k false
  map_target k t := evaluate_truncate x hx t k true
  map_comp k s t h h' := by
    rcases composable_has_identity k s t h with hs | ht
    · have hs' : s = truncate k false t :=
        ((complex n).nu.target_eq_self_of_source_eq_self hs).symm.trans h
      subst s
      erw [(complex n).nu.unit_left]
      revert h'
      rw [evaluate_truncate x hx t k false]
      intro h'
      exact (C.unit_left k (evaluate x t) h').symm
    · have ht' : t = truncate k true s := ht.symm.trans h.symm
      subst t
      erw [(complex n).nu.unit_right]
      revert h'
      rw [evaluate_truncate x hx s k true]
      intro h'
      exact (C.unit_right k (evaluate x s) h').symm

lemma lift_top {n : ℕ} {C : OmegaCategory.{v}} (x : C.Cell)
    (hx : C.source n x = x) : (lift.{u,v} x hx).map (topTable n) = x :=
  evaluate_top x hx

lemma functor_ext {n : ℕ} {C : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (complex.{u} n).nu C}
    (h : F.map (topTable n) = G.map (topTable n)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext t
  obtain ⟨p, b, _, rfl⟩ := table_classification t
  rw [← face_nu]
  erw [F.map_face, G.map_face, h]

end Thomason.GlobeComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}} {n : ℕ}

@[ext] theorem ext {f g : PartialHom K L n} (h : ∀ p, f.map p = g.map p) : f = g := by
  have hm : f.map = g.map := funext h
  cases f
  cases g
  cases hm
  rfl

end Thomason.DirectedComplex.PartialHom

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

variable {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

def constantAttachmentLabel : Y ⟶ interval :=
  H.desc (constantLabel X b) (posetCategorificationLabel l) (by
    rw [comp_constantLabel, posetCategorificationLabel_natural]
    exact (posetLabel_constant _ b hlA).symm)

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

theorem sieve_finite_attachment_covers (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsLowerSet S₁) (h₂ : IsLowerSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : A ⊆ S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.val.Objects,
      Y.val.IsObjectSieve T₁ ∧ Y.val.IsObjectSieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetFiniteAttachmentPiece n A S₁ hA₁ a h i T₁ ∧
      IsPosetFiniteAttachmentPiece n A S₂ hA₂ a h i T₂ ∧
      IsPosetFiniteAttachmentPiece n A (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩)
        a h i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := lowerSegmentLabel S₁ h₁
  let l₂ := lowerSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => max (l₁ p) (l₂ p),
    fun _ _ he => max_le_max (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 0 := fun p => (lowerSegmentLabel_zero S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := fun p => (lowerSegmentLabel_zero S₂ h₂ _).mpr (hA₂ p.property)
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change max (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 0} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      max (if p ∈ S₁ then (0 : Fin 2) else 1) (if p ∈ S₂ then 0 else 1) = 0
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantFiniteAttachmentLabel n hn A l₁ 0 hl₁ a h i H
  let η₂ := constantFiniteAttachmentLabel n hn A l₂ 0 hl₂ a h i H
  let η₃ := constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = maxFiniteLabel n hn η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_old n hn,comp_maxFiniteLabel,
        constantFiniteAttachmentLabel_old n hn,constantFiniteAttachmentLabel_old n hn]
      rfl
    · change i ≫ constantFiniteAttachmentLabel n hn A l₃ 0 hl₃ a h i H = _
      rw [constantFiniteAttachmentLabel_new n hn,comp_maxFiniteLabel,
        constantFiniteAttachmentLabel_new n hn,constantFiniteAttachmentLabel_new n hn]
      exact posetFiniteLabel_max n hn l₁ l₂
  have hp₃ := constant_finite_attachment_old_piece n hn A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩) hS₃
  change IsPosetFiniteAttachmentPiece n A (S₁ ∩ S₂) _ a h i (intervalFiberObjects η₃ 0) at hp₃
  rw [hη₃,maxFiniteLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 0,intervalFiberObjects η₂ 0,
    zero_fiber_isObjectSieve η₁,zero_fiber_isObjectSieve η₂,?_,
    constant_finite_attachment_old_piece n hn A l₁ 0 hl₁ a h i H S₁ hA₁ hS₁,
    constant_finite_attachment_old_piece n hn A l₂ 0 hl₂ a h i H S₂ hA₂ hS₂,hp₃⟩
  refine labelled_finite_objects_cover n hn H η₁ η₂ l₁ l₂ 0
    (Or.inl (constantFiniteAttachmentLabel_old n hn A l₁ 0 hl₁ a h i H))
    (constantFiniteAttachmentLabel_new n hn A l₁ 0 hl₁ a h i H)
    (constantFiniteAttachmentLabel_new n hn A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((lowerSegmentLabel_zero S₁ h₁ p).mpr) ((lowerSegmentLabel_zero S₂ h₂ p).mpr)

end Thomason.Attachments

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

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason

structure RightIntervalExtension where
  tensor : OmegaCategory.{u} ⥤ OmegaCategory.{u}
  endpoint : Bool → ((𝟭 OmegaCategory.{u}) ⟶ tensor)
  projection : tensor ⟶ (𝟭 OmegaCategory.{u})
  endpoint_projection : ∀ b, endpoint b ≫ projection = 𝟙 (𝟭 OmegaCategory.{u})
  cocontinuous : PreservesColimitsOfSize.{u,u} tensor
  rightAdjoint : tensor.IsLeftAdjoint
  simplex : ∀ (P : Type u) [LinearOrder P] [Finite P],
    tensor.obj (NormalizedChains.complex P).nu ≅
      (NormalizedChains.complex P).cylinder.nu
  simplex_natural : ∀ (P Q : Type u) [LinearOrder P] [Finite P]
      [LinearOrder Q] [Finite Q]
      (a : DirectedComplex.Hom (NormalizedChains.complex P) (NormalizedChains.complex Q)),
    tensor.map a.nu ≫ (simplex Q).hom = (simplex P).hom ≫ a.cylinder.nu
  simplex_endpoint : ∀ (P : Type u) [LinearOrder P] [Finite P] (b : Bool),
    (endpoint b).app (NormalizedChains.complex P).nu ≫ (simplex P).hom =
      ((NormalizedChains.complex P).cylinderEndpoint b).nu
  simplex_projection : ∀ (P : Type u) [LinearOrder P] [Finite P],
    (simplex P).hom ≫ (NormalizedChains.complex P).cylinderProjection.nu =
      projection.app (NormalizedChains.complex P).nu
  globe : ∀ n : ℕ, tensor.obj (GlobeComplex.complex.{u} n).nu ≅
    (GlobeComplex.complex.{u} n).cylinder.nu
  globe_natural : ∀ (n m : ℕ)
      (a : DirectedComplex.Hom (GlobeComplex.complex.{u} n) (GlobeComplex.complex.{u} m)),
    tensor.map a.nu ≫ (globe m).hom = (globe n).hom ≫ a.cylinder.nu
  globe_endpoint : ∀ (n : ℕ) (b : Bool),
    (endpoint b).app (GlobeComplex.complex.{u} n).nu ≫ (globe n).hom =
      ((GlobeComplex.complex.{u} n).cylinderEndpoint b).nu
  globe_projection : ∀ n : ℕ,
    (globe n).hom ≫ (GlobeComplex.complex.{u} n).cylinderProjection.nu =
      projection.app (GlobeComplex.complex.{u} n).nu

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def tableRowMap {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) (p : ℕ) :
    (complex.{u} n).Chain p →+ K.Chain p where
  toFun x := x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true
  map_zero' := by
    change (0 : chainModule.{u} n p).val ⟨false⟩ • t.row p false +
      (0 : chainModule.{u} n p).val ⟨true⟩ • t.row p true = 0
    simp
  map_add' x y := by
    change (x.val ⟨false⟩ + y.val ⟨false⟩) • t.row p false +
      (x.val ⟨true⟩ + y.val ⟨true⟩) • t.row p true =
      (x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true) +
        (y.val ⟨false⟩ • t.row p false + y.val ⟨true⟩ • t.row p true)
    simp only [add_smul]
    abel

lemma tableRowMap_d {K : DirectedComplex.{v}} (n : ℕ) (t : Table K)
    (p : ℕ) (x : (complex.{u} n).Chain (p+1)) :
    tableRowMap n t p ((complex n).d p x) =
      K.d p (tableRowMap n t (p+1) x) := by
  change ((complex n).d p x).val ⟨false⟩ • t.row p false +
      ((complex n).d p x).val ⟨true⟩ • t.row p true =
    K.d p (x.val ⟨false⟩ • t.row (p+1) false + x.val ⟨true⟩ • t.row (p+1) true)
  rw [complex_d_coordinate, complex_d_coordinate]
  simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_zsmul, t.boundary]
  change (-(x.val ⟨false⟩ + x.val ⟨true⟩)) • t.row p false +
      (x.val ⟨false⟩ + x.val ⟨true⟩) • t.row p true = _
  simp only [add_smul, neg_smul, smul_sub]
  abel

lemma tableRowMap_positive {K : DirectedComplex.{v}} (n : ℕ) (t : Table K)
    (p : ℕ) (x : (complex.{u} n).Chain p) (hx : x ∈ (complex n).positive p) :
    tableRowMap n t p x ∈ K.positive p := by
  change x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true ∈ K.positive p
  apply (K.positive p).add_mem
  · rw [← Int.toNat_of_nonneg (hx false), Nat.cast_smul_eq_nsmul]
    exact (K.positive p).nsmul_mem (t.positive p false) _
  · rw [← Int.toNat_of_nonneg (hx true), Nat.cast_smul_eq_nsmul]
    exact (K.positive p).nsmul_mem (t.positive p true) _

def tableMap {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) :
    Hom (complex.{u} n) K where
  map := tableRowMap n t
  map_d := tableRowMap_d n t
  map_augmentation x := by
    change K.augmentation (x.val ⟨false⟩ • t.row 0 false +
      x.val ⟨true⟩ • t.row 0 true) = x.val ⟨false⟩ + x.val ⟨true⟩
    simp only [map_add, map_zsmul, t.augmentation, zsmul_eq_mul, Int.cast_id, mul_one]
  map_positive := tableRowMap_positive n t

lemma tableMap_nu_top {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) :
    (tableMap.{u,v} n t).nu.map (topTable n) = truncate n false t := by
  change (tableMap n t).table (topTable n) = truncate n false t
  ext p b
  change tableRowMap n t p (topRow n p b) = _
  rw [truncate_row]
  by_cases hp : p < n
  · rw [ite_eq_left hp, topRow_lt n p b hp]
    cases b <;> simp [tableRowMap]
  · rw [ite_eq_right hp]
    by_cases hn : p = n
    · subst p
      rw [ite_eq_left rfl, topRow_eq]
      simp [tableRowMap]
    · rw [ite_eq_right hn, topRow_gt n p b (by omega), map_zero]

lemma tableMap_nu {K : DirectedComplex.{v}} {n : ℕ} (t : Table K)
    (ht : truncate n false t = t) :
    (tableMap.{u,v} n t).nu = lift t ht := by
  apply functor_ext
  erw [tableMap_nu_top, lift_top, ht]

def faceMap (n k : ℕ) (b : Bool) : Hom (complex.{u} k) (complex.{u} n) :=
  tableMap k (truncate k b (topTable n))

lemma faceMap_nu (n k : ℕ) (b : Bool) :
    (faceMap.{u} n k b).nu =
      lift (truncate k b (topTable n)) (by
        change truncate k false (truncate k b (topTable n)) = truncate k b (topTable n)
        simp only [truncate_truncate, lt_self_iff_false, ite_false]) :=
  tableMap_nu _ _

lemma chain_eq_topRows {n p : ℕ} (x : (complex.{u} n).Chain p) :
    x = x.val ⟨false⟩ • topRow n p false + x.val ⟨true⟩ • topRow n p true := by
  by_cases hp : p < n
  · rw [topRow_lt n p false hp, topRow_lt n p true hp]
    apply Subtype.ext
    funext ⟨i⟩
    change x.val ⟨i⟩ = x.val ⟨false⟩ * (if i = false then 1 else 0) +
      x.val ⟨true⟩ * (if i = true then 1 else 0)
    cases i <;> simp
  · by_cases hn : p = n
    · subst p
      rw [topRow_eq, topRow_eq]
      have ht := top_target_zero n x
      apply Subtype.ext
      funext ⟨i⟩
      change x.val ⟨i⟩ = x.val ⟨false⟩ * (if i = false then 1 else 0) +
        x.val ⟨true⟩ * (if i = false then 1 else 0)
      cases i <;> simp [ht]
    · rw [chain_zero (show n < p by omega) x]
      simp
      rfl

lemma hom_ext {K : DirectedComplex.{v}} {n : ℕ}
    {f g : Hom (complex.{u} n) K}
    (h : f.nu.map (topTable n) = g.nu.map (topTable n)) : f = g := by
  ext p x
  change f.table (topTable n) = g.table (topTable n) at h
  have h₀ := congrArg (fun t : Table K => t.row p false) h
  have h₁ := congrArg (fun t : Table K => t.row p true) h
  change f.map p (topRow n p false) = g.map p (topRow n p false) at h₀
  change f.map p (topRow n p true) = g.map p (topRow n p true) at h₁
  rw [chain_eq_topRows x]
  simp only [map_add, map_zsmul, h₀, h₁]

lemma faceMap_top (n k : ℕ) (b : Bool) :
    (faceMap.{u} n k b).nu.map (topTable k) = truncate k b (topTable n) := by
  erw [faceMap_nu, lift_top]

@[simp] lemma faceMap_self (n : ℕ) (b : Bool) :
    faceMap.{u} n n b = Hom.id (complex n) := by
  apply hom_ext
  rw [faceMap_top]
  change truncate n b (topTable n) = topTable n
  rw [← face_nu]
  exact (complex n).nu.face_of_fixed (topTable_bounded n) (le_refl n) b

end Thomason.GlobeComplex

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

lemma join_target_le (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hik : i ≤ k) (h : C.target k x = C.source k y) :
    C.target i (C.join k x y) = C.target i y := by
  rw [C.join_eq k x y h, C.target_comp_le i k hik]
lemma join_source_gt (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hki : k < i) (h : C.target k x = C.source k y) :
    C.source i (C.join k x y) = C.join k (C.source i x) (C.source i y) := by
  rw [C.join_eq k x y h, C.join_eq k _ _ (C.source_composable hki h),
    C.source_comp_gt i k hki]
lemma join_target_gt (C : OmegaCategory.{u}) (i k : ℕ) (x y : C.Cell)
    (hki : k < i) (h : C.target k x = C.source k y) :
    C.target i (C.join k x y) = C.join k (C.target i x) (C.target i y) := by
  rw [C.join_eq k x y h, C.join_eq k _ _ (C.target_composable hki h),
    C.target_comp_gt i k hki]

lemma join_left_unit (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (hx : C.source k x = x) (h : C.target k x = C.source k y) :
    C.join k x y = y := by
  rw [C.join_eq k x y h, C.comp_of_left_source_fixed k x y h hx]
lemma join_right_unit (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell)
    (hy : C.source k y = y) (h : C.target k x = C.source k y) :
    C.join k x y = x := by
  rw [C.join_eq k x y h, C.comp_of_right_source_fixed k x y h hy]

lemma join_assoc (C : OmegaCategory.{u}) (k : ℕ) (x y z : C.Cell)
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.join k (C.join k x y) z = C.join k x (C.join k y z) := by
  rw [C.join_eq k x y hxy, C.join_eq k y z hyz,
    C.join_eq k _ z (C.assoc_composable_left hxy hyz),
    C.join_eq k x _ (C.assoc_composable_right hxy hyz)]
  exact C.assoc k x y z _ _ _ _

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

@[simp] lemma positive_shiftDown (n p : ℕ) (x : Chain.{u} (n+1) (p+1)) :
    shiftDown n p x ∈ (complex n).positive p ↔ x ∈ (complex (n+1)).positive (p+1) := Iff.rfl

@[simp] lemma positive_shiftUp (n p : ℕ) (x : Chain.{u} n p) :
    (shiftDown n p).symm x ∈ (complex (n+1)).positive (p+1) ↔
      x ∈ (complex n).positive p := Iff.rfl

lemma shiftDown_d (n p : ℕ) (x : Chain.{u} (n+1) (p+2)) :
    shiftDown n p ((complex (n+1)).d (p+1) x) =
      (complex n).d p (shiftDown n (p+1) x) := by
  apply Subtype.ext
  funext ⟨i⟩
  change (((complex (n+1)).d (p+1) x).val ⟨i⟩) = _
  erw [complex_d_coordinate, complex_d_coordinate, mass_shiftDown]

lemma shiftUp_d (n p : ℕ) (x : Chain.{u} n (p+1)) :
    (complex (n+1)).d (p+1) ((shiftDown n (p+1)).symm x) =
      (shiftDown n p).symm ((complex n).d p x) := by
  apply (shiftDown n p).injective
  erw [shiftDown_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def vertexWeights (n : ℕ) (a b : ℤ) : Chain.{u} (n+1) 0 :=
  ⟨fun i => if i.down then b else a, by intro i hi; rcases hi with h | ⟨h, _⟩ <;> omega⟩

@[simp] lemma vertexWeights_coordinate (n : ℕ) (a b : ℤ) (i : Bool) :
    (vertexWeights.{u} n a b).val ⟨i⟩ = if i then b else a := rfl

@[simp] lemma vertexWeights_zero (n : ℕ) : vertexWeights.{u} n 0 0 = 0 := by
  apply Subtype.ext
  funext ⟨i⟩
  cases i <;> rfl

lemma vertexWeights_positive {n : ℕ} {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    vertexWeights.{u} n a b ∈ (complex (n+1)).positive 0 := by
  intro i
  cases i <;> assumption

lemma d_shiftUp_zero (n : ℕ) (x : Chain.{u} n 0) :
    (complex (n+1)).d 0 ((shiftDown n 0).symm x) =
      vertexWeights n (-mass n 0 x) (mass n 0 x) := by
  apply Subtype.ext
  funext ⟨i⟩
  erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate]

lemma vertexWeights_add (n : ℕ) (a b c d : ℤ) :
    vertexWeights.{u} n (a+c) (b+d) = vertexWeights n a b + vertexWeights n c d := by
  apply Subtype.ext
  funext ⟨i⟩
  cases i <;> rfl

lemma mass_d (n p : ℕ) (x : Chain.{u} n (p+1)) :
    mass n p ((complex n).d p x) = 0 := by
  change mass n p (mass n (p+1) x • delta n p) = 0
  rw [map_zsmul, mass_delta, smul_zero]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

abbrev K (n : ℕ) : DirectedComplex.{u} := (complex n).cylinder

def diagonalRow (n : ℕ) (b : Bool) : (K.{u} (n+1)).Chain 0 :=
  if b then (0, basis (n+1) 0 true (Or.inl (by omega)))
  else (basis (n+1) 0 false (Or.inl (by omega)), 0)

def IsDiagonal {n : ℕ} (t : Table (K.{u} (n+1))) : Prop :=
  ∀ b, t.row 0 b = diagonalRow n b

def downRow (n : ℕ) : (p : ℕ) → (K.{u} (n+1)).Chain (p+1) →+ (K.{u} n).Chain p
  | 0 =>
    { toFun x := (shiftDown n 0 x.2.1, shiftDown n 0 x.1)
      map_zero' := rfl
      map_add' _ _ := rfl }
  | p+1 =>
    { toFun x := (shiftDown n (p+1) x.2.1, shiftDown n (p+1) x.1,
      shiftDown n p x.2.2)
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma downRow_d (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+2)) :
    downRow n p ((K (n+1)).d (p+1) x) = (K n).d p (downRow n (p+1) x) := by
  cases p with
  | zero =>
    apply Prod.ext
    · change shiftDown n 0 ((complex (n+1)).d 1 x.2.1 + (-1 : ℤ) • x.2.2) =
        differential n 0 (shiftDown n 1 x.2.1) - shiftDown n 0 x.2.2
      erw [map_add, map_zsmul (shiftDown n 0) (-1) x.2.2, shiftDown_d]
      simp [complex, sub_eq_add_neg]
      rfl
    · change shiftDown n 0 ((complex (n+1)).d 1 x.1 - (-1 : ℤ) • x.2.2) =
        differential n 0 (shiftDown n 1 x.1) + shiftDown n 0 x.2.2
      erw [map_sub, map_zsmul (shiftDown n 0) (-1) x.2.2, shiftDown_d]
      simp [complex]
      rfl
  | succ p =>
    apply Prod.ext
    · change shiftDown n (p+1) ((complex (n+1)).d (p+2) x.2.1 +
        (-1 : ℤ)^(p+2) • x.2.2) =
          differential n (p+1) (shiftDown n (p+2) x.2.1) -
          (-1 : ℤ)^(p+1) • shiftDown n (p+1) x.2.2
      erw [map_add, map_zsmul (shiftDown n (p+1)) ((-1)^(p+2)) x.2.2, shiftDown_d]
      simp [complex, pow_succ, sub_eq_add_neg]
      rfl
    · apply Prod.ext
      · change shiftDown n (p+1) ((complex (n+1)).d (p+2) x.1 -
          (-1 : ℤ)^(p+2) • x.2.2) =
            differential n (p+1) (shiftDown n (p+2) x.1) +
            (-1 : ℤ)^(p+1) • shiftDown n (p+1) x.2.2
        erw [map_sub, map_zsmul (shiftDown n (p+1)) ((-1)^(p+2)) x.2.2, shiftDown_d]
        simp [complex, pow_succ, sub_eq_add_neg]
        rfl
      · exact shiftDown_d n p x.2.2

lemma downRow_positive (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+1))
    (hx : x ∈ (K (n+1)).positive (p+1)) :
    downRow n p x ∈ (K n).positive p := by
  cases p with
  | zero => exact ⟨hx.2.1, hx.1⟩
  | succ p => exact ⟨hx.2.1, hx.1, hx.2.2⟩

lemma diagonal_row_one {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    mass (n+1) 1 (t.row 1 b).1 + mass (n+1) 1 (t.row 1 b).2.1 = 1 ∧
      (t.row 1 b).2.2 = vertexWeights n (mass (n+1) 1 (t.row 1 b).2.1)
        (mass (n+1) 1 (t.row 1 b).1) := by
  have h := t.boundary 0 b
  rw [ht true, ht false] at h
  have h₀ := congrArg (fun x : (K (n+1)).Chain 0 => x.1.val ⟨false⟩) h
  have h₁ := congrArg (fun x : (K (n+1)).Chain 0 => x.1.val ⟨true⟩) h
  have h₂ := congrArg (fun x : (K (n+1)).Chain 0 => x.2.val ⟨false⟩) h
  change (((complex (n+1)).d 0 (t.row 1 b).1).val ⟨false⟩) -
    (t.row 1 b).2.2.val ⟨false⟩ = -1 at h₀
  change (((complex (n+1)).d 0 (t.row 1 b).1).val ⟨true⟩) -
    (t.row 1 b).2.2.val ⟨true⟩ = 0 at h₁
  change (((complex (n+1)).d 0 (t.row 1 b).2.1).val ⟨false⟩) +
    (t.row 1 b).2.2.val ⟨false⟩ = 0 at h₂
  erw [complex_d_coordinate] at h₀ h₁ h₂
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁ h₂
  dsimp [mass] at h₀ h₁ h₂ ⊢
  refine ⟨by omega, ?_⟩
  apply Subtype.ext
  funext ⟨i⟩
  change (t.row 1 b).2.2.val ⟨i⟩ = if i then _ else _
  cases i <;> dsimp [mass] <;> omega

def down {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) : Table (K.{u} n) where
  row p b := downRow n p (t.row (p+1) b)
  positive p b := downRow_positive n p _ (t.positive (p+1) b)
  boundary p b := by
    rw [← downRow_d, t.boundary, map_sub]
  augmentation b := by
    change mass (n+1) 1 (t.row 1 b).2.1 + mass (n+1) 1 (t.row 1 b).1 = 1
    rw [add_comm]
    exact (diagonal_row_one t ht b).1
  bounded := by
    obtain ⟨k, hk⟩ := t.bounded
    refine ⟨k, fun p hp b => ?_⟩
    rw [hk (p+1) (by omega) b, map_zero]

@[simp] lemma down_row {n p : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    (down t ht).row p b = downRow n p (t.row (p+1) b) := rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def upRow (n : ℕ) : (p : ℕ) → (K.{u} n).Chain p →+ (K.{u} (n+1)).Chain (p+1)
  | 0 =>
    { toFun x := ((shiftDown n 0).symm x.2, (shiftDown n 0).symm x.1,
        vertexWeights n (mass n 0 x.1) (mass n 0 x.2))
      map_zero' := by
        apply Prod.ext
        · rfl
        · exact Prod.ext rfl (vertexWeights_zero n)
      map_add' first second := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · change vertexWeights n (mass n 0 (first.1 + second.1))
              (mass n 0 (first.2 + second.2)) = _
            erw [map_add, map_add]
            exact vertexWeights_add n _ _ _ _ }
  | p+1 =>
    { toFun x := ((shiftDown n (p+1)).symm x.2.1, (shiftDown n (p+1)).symm x.1,
        (shiftDown n p).symm x.2.2)
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma upRow_d_zero (n : ℕ) (x : (K.{u} n).Chain 1) :
    upRow n 0 ((K n).d 0 x) = (K (n+1)).d 1 (upRow n 1 x) := by
  apply Prod.ext
  · change (shiftDown n 0).symm ((complex n).d 0 x.2.1 + x.2.2) =
      differential (n+1) 1 ((shiftDown n 1).symm x.2.1) -
        (-1 : ℤ) • (shiftDown n 0).symm x.2.2
    erw [map_add, shiftUp_d]
    simp
  · apply Prod.ext
    · change (shiftDown n 0).symm ((complex n).d 0 x.1 - x.2.2) =
        differential (n+1) 1 ((shiftDown n 1).symm x.1) +
          (-1 : ℤ) • (shiftDown n 0).symm x.2.2
      erw [map_sub, shiftUp_d]
      simp [sub_eq_add_neg]
    · change vertexWeights n (mass n 0 ((complex n).d 0 x.1 - x.2.2))
        (mass n 0 ((complex n).d 0 x.2.1 + x.2.2)) =
          (complex (n+1)).d 0 ((shiftDown n 0).symm x.2.2)
      erw [map_sub, map_add, mass_d, mass_d, d_shiftUp_zero]
      simp only [zero_sub, zero_add]

lemma upRow_d_succ (n p : ℕ) (x : (K.{u} n).Chain (p+2)) :
    upRow n (p+1) ((K n).d (p+1) x) =
      (K (n+1)).d (p+2) (upRow n (p+2) x) := by
  apply Prod.ext
  · change (shiftDown n (p+1)).symm ((complex n).d (p+1) x.2.1 +
      (-1 : ℤ)^(p+1) • x.2.2) =
        differential (n+1) (p+2) ((shiftDown n (p+2)).symm x.2.1) -
          (-1 : ℤ)^(p+2) • (shiftDown n (p+1)).symm x.2.2
    erw [map_add, map_zsmul (shiftDown n (p+1)).symm ((-1)^(p+1)) x.2.2, shiftUp_d]
    simp [pow_succ, sub_eq_add_neg]
    rfl
  · apply Prod.ext
    · change (shiftDown n (p+1)).symm ((complex n).d (p+1) x.1 -
        (-1 : ℤ)^(p+1) • x.2.2) =
          differential (n+1) (p+2) ((shiftDown n (p+2)).symm x.1) +
            (-1 : ℤ)^(p+2) • (shiftDown n (p+1)).symm x.2.2
      erw [map_sub, map_zsmul (shiftDown n (p+1)).symm ((-1)^(p+1)) x.2.2, shiftUp_d]
      simp [pow_succ, sub_eq_add_neg]
      rfl
    · change (shiftDown n p).symm ((complex n).d p x.2.2) =
        (complex (n+1)).d (p+1) ((shiftDown n (p+1)).symm x.2.2)
      exact (shiftUp_d n p x.2.2).symm

lemma upRow_d (n p : ℕ) (x : (K.{u} n).Chain (p+1)) :
    upRow n p ((K n).d p x) = (K (n+1)).d (p+1) (upRow n (p+1) x) := by
  cases p with
  | zero => exact upRow_d_zero n x
  | succ p => exact upRow_d_succ n p x

lemma upRow_positive (n p : ℕ) (x : (K.{u} n).Chain p) (hx : x ∈ (K n).positive p) :
    upRow n p x ∈ (K (n+1)).positive (p+1) := by
  cases p with
  | zero => exact ⟨hx.2, hx.1, vertexWeights_positive (mass_nonneg hx.1) (mass_nonneg hx.2)⟩
  | succ p => exact ⟨hx.2.1, hx.1, hx.2.2⟩

lemma upRow_zero_d (n : ℕ) (x : (K.{u} n).Chain 0) (hx : (K n).augmentation x = 1) :
    (K (n+1)).d 0 (upRow n 0 x) = diagonalRow n true - diagonalRow n false := by
  change mass n 0 x.1 + mass n 0 x.2 = 1 at hx
  apply Prod.ext
  · apply Subtype.ext
    funext ⟨i⟩
    change (((complex (n+1)).d 0 ((shiftDown n 0).symm x.2)).val ⟨i⟩) -
      (vertexWeights.{u} n (mass n 0 x.1) (mass n 0 x.2)).val ⟨i⟩ =
      0 - (basis.{u} (n+1) 0 false (Or.inl (by omega))).val ⟨i⟩
    erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate, basis_coordinate]
    cases i <;> dsimp <;> omega
  · apply Subtype.ext
    funext ⟨i⟩
    change (((complex (n+1)).d 0 ((shiftDown n 0).symm x.1)).val ⟨i⟩) +
      (vertexWeights.{u} n (mass n 0 x.1) (mass n 0 x.2)).val ⟨i⟩ =
      (basis.{u} (n+1) 0 true (Or.inl (by omega))).val ⟨i⟩ - 0
    erw [complex_d_coordinate, mass_shiftUp, vertexWeights_coordinate, basis_coordinate]
    cases i <;> dsimp <;> omega

def up {n : ℕ} (t : Table (K.{u} n)) : Table (K.{u} (n+1)) where
  row
    | 0, b => diagonalRow n b
    | p+1, b => upRow n p (t.row p b)
  positive p b := by
    cases p with
    | zero =>
      cases b
      · exact ⟨basis_positive _ _ _ (Or.inl (by omega)), (complex (n+1)).positive 0 |>.zero_mem⟩
      · exact ⟨(complex (n+1)).positive 0 |>.zero_mem, basis_positive _ _ _ (Or.inl (by omega))⟩
    | succ p => exact upRow_positive n p _ (t.positive p b)
  boundary p b := by
    cases p with
    | zero => exact upRow_zero_d n (t.row 0 b) (t.augmentation b)
    | succ p => rw [← upRow_d, t.boundary, map_sub]
  augmentation b := by
    change mass (n+1) 0 (diagonalRow n b).1 + mass (n+1) 0 (diagonalRow n b).2 = 1
    cases b <;> simp [diagonalRow, mass, basis] <;> rfl
  bounded := by
    obtain ⟨k, hk⟩ := t.bounded
    refine ⟨k+1, ?_⟩
    rintro (_ | p) hp b
    · omega
    · change upRow n p (t.row p b) = 0
      rw [hk p (by omega) b, map_zero]

@[simp] lemma up_zero {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    (up t).row 0 b = diagonalRow n b := rfl

@[simp] lemma up_succ {n p : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    (up t).row (p+1) b = upRow n p (t.row p b) := rfl

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Generation. -/

noncomputable section
universe u v w z
open CategoryTheory

namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def corner (n : ℕ) (b : Bool) : Table (K.{u} (n+1)) where
  row
    | 0, _ => diagonalRow n b
    | _+1, _ => 0
  positive p e := by
    cases p with
    | zero =>
      cases b
      · exact ⟨basis_positive _ _ _ (Or.inl (by omega)), (complex (n+1)).positive 0 |>.zero_mem⟩
      · exact ⟨(complex (n+1)).positive 0 |>.zero_mem, basis_positive _ _ _ (Or.inl (by omega))⟩
    | succ p => exact (K (n+1)).positive (p+1) |>.zero_mem
  boundary p e := by cases p <;> simp
  augmentation e := by
    change mass (n+1) 0 (diagonalRow n b).1 + mass (n+1) 0 (diagonalRow n b).2 = 1
    cases b <;> simp [diagonalRow, mass, basis] <;> rfl
  bounded := ⟨0, by
    rintro (_ | p) hp e
    · omega
    · rfl⟩

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def sideRow {n : ℕ} (t : Table (K.{u} n)) (a : Bool) : (p : ℕ) → Bool → (complex.{u} n).Chain p
  | 0, b => if a then (t.row 0 b).2 else (t.row 0 b).1
  | p+1, b => if a then (t.row (p+1) b).2.1 else (t.row (p+1) b).1

def crossRow {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) : (complex.{u} n).Chain p :=
  (t.row (p+1) b).2.2

def project {n : ℕ} (t : Table (K.{u} n)) : Table (complex.{u} n) :=
  (complex n).cylinderProjection.table t

lemma project_row {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (project t).row p b = sideRow t false p b + sideRow t true p b := by cases p <;> rfl

lemma side_positive {n : ℕ} (t : Table (K.{u} n)) (a : Bool) (p : ℕ) (b : Bool) :
    sideRow t a p b ∈ (complex n).positive p := by
  cases p with
  | zero => cases a; exact (t.positive 0 b).1; exact (t.positive 0 b).2
  | succ p => cases a; exact (t.positive (p+1) b).1; exact (t.positive (p+1) b).2.1

lemma cross_positive {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    crossRow t p b ∈ (complex n).positive p := (t.positive (p+1) b).2.2

lemma right_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (sideRow t true (p+1) b) + (-1 : ℤ)^p • crossRow t p b =
      sideRow t true p true - sideRow t true p false := by
  cases p with
  | zero => simpa [sideRow, crossRow, cylinderDifferential] using congrArg Prod.snd (t.boundary 0 b)
  | succ p => exact congrArg (fun x : (K n).Chain (p+1) => x.2.1) (t.boundary (p+1) b)

lemma side_augmentation {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    mass n 0 (sideRow t false 0 b) + mass n 0 (sideRow t true 0 b) = 1 := t.augmentation b

lemma side_mass_vertex {n : ℕ} (t : Table (K.{u} n)) (a b : Bool) :
    mass n 0 (sideRow t a 0 b) = 0 ∨ mass n 0 (sideRow t a 0 b) = 1 := by
  have h := side_augmentation t b
  have h₀ := mass_nonneg (side_positive t false 0 b)
  have h₁ := mass_nonneg (side_positive t true 0 b)
  cases a <;> omega

lemma cross_mass_vertex {n : ℕ} (t : Table (K.{u} n)) (b : Bool) :
    mass n 0 (crossRow t 0 b) =
      mass n 0 (sideRow t true 0 true) - mass n 0 (sideRow t true 0 false) := by
  have h := congrArg (mass n 0) (right_boundary t 0 b)
  simp only [pow_zero, one_smul] at h
  erw [map_add, map_sub, mass_d] at h
  simpa using h

lemma interval_monotone {n : ℕ} (t : Table (K.{u} n)) :
    mass n 0 (sideRow t true 0 false) ≤ mass n 0 (sideRow t true 0 true) := by
  have h := mass_nonneg (cross_positive t 0 false)
  rw [cross_mass_vertex] at h
  omega

lemma crossing_sides {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false)) :
    sideRow t true 0 false = 0 ∧ sideRow t false 0 true = 0 := by
  have hs := side_mass_vertex t true false
  have ht := side_mass_vertex t true true
  have hm := interval_monotone t
  have ha := side_augmentation t true
  constructor
  · apply (mass_eq_zero_iff (side_positive t true 0 false)).mp
    omega
  · apply (mass_eq_zero_iff (side_positive t false 0 true)).mp
    omega

lemma crossing_vertices {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false)) :
    (∀ b, sideRow t b 0 b = (project t).row 0 b) := by
  obtain ⟨hs, ht⟩ := crossing_sides t h
  intro b
  rw [project_row]
  cases b
  · rw [hs, add_zero]
  · rw [ht, zero_add]

lemma crossing_diagonal {n : ℕ} (t : Table (K.{u} (n+1)))
    (h : mass (n+1) 0 (sideRow t true 0 true) ≠ mass (n+1) 0 (sideRow t true 0 false))
    {p : ℕ} (hp : 0 < p) (e : Bool)
    (hpj : project t = truncate p e (topTable (n+1))) : IsDiagonal t := by
  have hv := crossing_vertices t h
  obtain ⟨hs, ht⟩ := crossing_sides t h
  intro b
  have hb := hv b
  rw [hpj, truncate_row, ite_eq_left hp] at hb
  change sideRow t b 0 b = topRow (n+1) 0 b at hb
  rw [topRow_lt _ _ _ (by omega)] at hb
  cases b
  · exact Prod.ext hb hs
  · exact Prod.ext ht hb

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open DirectedComplex DirectedComplex.Table

def suspendTable {n : ℕ} (x : Table (complex.{u} n)) : Table (complex.{u} (n+1)) where
  row
    | 0, b => basis (n+1) 0 b (Or.inl (by omega))
    | p+1, b => (shiftDown n p).symm (x.row p b)
  positive p b := by
    cases p with
    | zero => exact basis_positive _ _ _ _
    | succ p => exact x.positive p b
  boundary p b := by
    cases p with
    | zero =>
      erw [d_shiftUp_zero, table_mass_zero]
      apply Subtype.ext
      funext ⟨i⟩
      change (if i then (1 : ℤ) else -1) =
        (basis.{u} (n+1) 0 true (Or.inl (by omega))).val ⟨i⟩ -
        (basis.{u} (n+1) 0 false (Or.inl (by omega))).val ⟨i⟩
      cases i <;> simp
    | succ p => erw [shiftUp_d, x.boundary, map_sub]; rfl
  augmentation b := mass_basis _ _ _ _
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k+1, ?_⟩
    rintro (_ | p) hp b
    · omega
    · change (shiftDown n p).symm (x.row p b) = 0
      erw [hk p (by omega) b, map_zero]

@[simp] lemma suspendTable_zero {n : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    (suspendTable x).row 0 b = basis (n+1) 0 b (Or.inl (by omega)) := rfl

@[simp] lemma suspendTable_succ {n p : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    (suspendTable x).row (p+1) b = (shiftDown n p).symm (x.row p b) := rfl

lemma suspendTable_truncate {n : ℕ} (x : Table (complex.{u} n)) (k : ℕ) (b : Bool) :
    suspendTable (truncate k b x) = truncate (k+1) b (suspendTable x) := by
  ext p a
  cases p with
  | zero => simp
  | succ p =>
    simp only [suspendTable_succ, truncate_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    erw [apply_ite (shiftDown n p).symm, apply_ite (shiftDown n p).symm, map_zero]
    rfl

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

def atEnd {n : ℕ} (a : Bool) (x : Table (complex.{u} n)) : Table (K.{u} n) :=
  ((complex n).cylinderEndpoint a).table x

def vertex (n : ℕ) (a : Bool) : Table (complex.{u} (n+1)) := truncate 0 a (topTable (n+1))

@[simp] lemma vertex_zero (n : ℕ) (a b : Bool) :
    (vertex.{u} n a).row 0 b = basis (n+1) 0 a (Or.inl (by omega)) := by
  simp [vertex, topTable, topRow_lt _ _ _ (show 0 < n+1 by omega)]

@[simp] lemma vertex_succ (n p : ℕ) (a b : Bool) : (vertex.{u} n a).row (p+1) b = 0 := by
  simp [vertex]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma project_fixed {n k : ℕ} (t : Table (K.{u} n))
    (h : truncate k false t = t) : truncate k false (project t) = project t := by
  change truncate k false ((complex n).cylinderProjection.table t) = _
  rw [← Hom.table_truncate, h]
  rfl

lemma suspend_fixed {n k : ℕ} (t : Table (complex.{u} n))
    (h : truncate k false t = t) : truncate (k+1) false (suspendTable t) = suspendTable t := by
  rw [← suspendTable_truncate, h]

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_IntervalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval Extension. -/

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

lemma bounded_table_classification {i k : ℕ} (t : Table (complex.{u} i))
    (ht : truncate k false t = t) :
    ∃ p b, p ≤ i ∧ p ≤ k ∧ t = truncate p b (topTable i) := by
  obtain ⟨p,b,hpi,he⟩ := table_classification t
  refine ⟨p,b,hpi,?_,he⟩
  by_contra hn
  have hkp : k < p := by omega
  rw [he, truncate_truncate, ite_eq_left hkp] at ht
  have hp := top_face_dimension (hkp.le.trans hpi) hpi false b ht
  omega

def sourceCollapse (i k : ℕ) : Hom (complex.{u} i) (complex.{u} i) :=
  tableMap i (truncate k false (topTable i))

lemma sourceCollapse_top (i k : ℕ) :
    (sourceCollapse.{u} i k).nu.map (topTable i) = truncate k false (topTable i) := by
  rw [sourceCollapse, tableMap_nu_top]
  change (complex i).nu.source i ((complex i).nu.source k (topTable i)) = _
  erw [(complex i).nu.source_source, min_comm, ← (complex i).nu.source_source]
  change truncate k false (truncate i false (topTable i)) = _
  rw [topTable_bounded]

lemma sourceCollapse_bounded {i k r : ℕ} (hrk : r < k) (t : Table (complex.{u} i))
    (ht : truncate r false t = t) : (sourceCollapse i k).nu.map t = t := by
  obtain ⟨p,b,_,hpr,rfl⟩ := bounded_table_classification t ht
  change (sourceCollapse i k).table (truncate p b (topTable i)) = _
  rw [Hom.table_truncate]
  change truncate p b ((sourceCollapse i k).nu.map (topTable i)) = _
  rw [sourceCollapse_top, truncate_truncate, ite_eq_left (by omega)]

lemma sourceCollapse_comp_truncated {i k : ℕ} {Y : OmegaCategory.{v}}
    (hk : Y.IsTruncated k) (F : OmegaCategory.Functor (complex.{u} i).nu Y) :
    OmegaCategory.Functor.comp (sourceCollapse i k).nu F = F := by
  apply functor_ext
  change F.map ((sourceCollapse i k).nu.map (topTable i)) = F.map (topTable i)
  rw [sourceCollapse_top]
  change F.map ((complex i).nu.source k (topTable i)) = F.map (topTable i)
  erw [F.map_source, hk]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma cylinder_map_endpoint {i j : ℕ} (f : Hom (complex.{u} i) (complex.{u} j))
    (a : Bool) (x : Table (complex i)) :
    f.cylinder.nu.map (atEnd a x) = atEnd a (f.nu.map x) :=
  congrArg (fun g : Hom (complex i) (K j) => g.nu.map x) (f.cylinder_endpoint a)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Simplicial MonoidalCategory Opposite
open DirectedComplex NormalizedChains OmegaCategory

variable (T : RightIntervalExtension.{u})

def cut {P : Type u} [LinearOrder P] [Finite P] (θ : P →o Fin 2) :
    (complex P).nu ⟶ T.tensor.obj (complex P).nu :=
  (awHom θ).nu ≫ (T.simplex P).inv

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData
open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def finiteAntihomotopy (σ : P →o E) :
    PositiveAntihomotopy (complexMap (d.finiteImageLeft σ))
      (complexMap (d.finiteImageRight σ)) := by
  refine PositiveAntihomotopy.lift (complexMap (d.finiteImageLeft σ))
    (complexMap (d.finiteImageRight σ)) (complexMap (d.finiteImage σ).inclusion)
    ?_ (d.antihomotopy.precomp (complexMap σ)) ?_ ?_
    (gradedPrism (d.finiteImageLeft σ) (d.finiteImageRight σ)) ?_ ?_
  · intro p x y h
    apply Subtype.ext
    have hv : map (d.finiteImage σ).inclusion x.val =
        map (d.finiteImage σ).inclusion y.val :=
      congrArg (fun z : grade (E := E) (p+1) => z.val) h
    apply map_orderEmbedding_injective
      (OrderEmbedding.subtype (d.finiteImage σ).vertices)
    exact hv
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion (map (d.finiteImageLeft σ) x.val) =
      map d.f (map σ x.val)
    simp only [← map_comp]
    rfl
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion (map (d.finiteImageRight σ) x.val) =
      map d.g (map σ x.val)
    simp only [← map_comp]
    rfl
  · intro p x hx
    exact prism_positive _ _ hx
  · intro p x
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (_root_.OAI.Thomason.NormalizedChains.prism (d.finiteImageLeft σ) (d.finiteImageRight σ) x.val) =
      _root_.OAI.Thomason.NormalizedChains.prism d.f d.g (map σ x.val)
    rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
    rfl

def finiteCylinderChainMap (σ : P →o E) :
    Hom (complex P).cylinder (complex (d.finiteImage σ).vertices) :=
  (d.finiteAntihomotopy σ).cylinderHom

lemma finiteCylinderChainMap_inclusion (σ : P →o E) :
    Hom.comp (d.finiteCylinderChainMap σ) (complexMap (d.finiteImage σ).inclusion) =
      Hom.comp (complexMap σ).cylinder d.cylinderChainMap := by
  ext p x
  cases p with
  | zero =>
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (map (d.finiteImageLeft σ) x.1.val + map (d.finiteImageRight σ) x.2.val) =
      map d.f (map σ x.1.val) + map d.g (map σ x.2.val)
    simp only [map_add, ← map_comp]
    rfl
  | succ p =>
    apply Subtype.ext
    change map (d.finiteImage σ).inclusion
      (map (d.finiteImageLeft σ) x.1.val + map (d.finiteImageRight σ) x.2.1.val +
        _root_.OAI.Thomason.NormalizedChains.prism (d.finiteImageLeft σ) (d.finiteImageRight σ) x.2.2.val) =
      map d.f (map σ x.1.val) + map d.g (map σ x.2.1.val) +
        _root_.OAI.Thomason.NormalizedChains.prism d.f d.g (map σ x.2.2.val)
    simp only [map_add, ← map_comp]
    rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
    rfl

lemma finiteCylinderChainMap_natural (σ : Q →o E) (α : P →o Q) :
    Hom.comp (d.finiteCylinderChainMap (σ.comp α))
      (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
        (d.finiteImage_mono σ α))) =
      Hom.comp (complexMap α).cylinder (d.finiteCylinderChainMap σ) := by
  ext p x
  apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype (d.finiteImage σ).vertices) p
  have hl := congrArg (fun h => h.map p x) (d.finiteCylinderChainMap_inclusion (σ.comp α))
  have hr := congrArg (fun h => h.map p ((complexMap α).cylinder.map p x))
    (d.finiteCylinderChainMap_inclusion σ)
  have he : Hom.comp (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
      (d.finiteImage_mono σ α))) (complexMap (d.finiteImage σ).inclusion) =
      complexMap (d.finiteImage (σ.comp α)).inclusion := by
    rw [← complexMap_comp]; rfl
  have hc : Hom.comp (complexMap α).cylinder (complexMap σ).cylinder =
      (complexMap (σ.comp α)).cylinder := by rw [complexMap_comp, Hom.cylinder_comp]
  change (Hom.comp (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
      (d.finiteImage_mono σ α))) (complexMap (d.finiteImage σ).inclusion)).map p
      ((d.finiteCylinderChainMap (σ.comp α)).map p x) = _
  rw [he]
  dsimp only [Hom.comp, AddMonoidHom.comp_apply] at hl hr ⊢
  exact hl.trans ((congrArg (fun h => d.cylinderChainMap.map p (h.map p x)) hc.symm).trans hr.symm)

end Thomason.RelativePrismData

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


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u})
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def prismLeg (σ : P →o E) :
    T.tensor.obj (categorification.obj (nerve P)) ⟶ categorification.obj (nerve E) :=
  T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫
    (d.finiteCylinderChainMap σ).nu ≫ (d.finiteImage σ).lift

lemma prismLeg_natural (σ : Q →o E) (α : P →o Q) :
    T.tensor.map (categorification.map (nerveMap α.monotone.functor)) ≫ d.prismLeg T σ =
      d.prismLeg T (σ.comp α) := by
  unfold prismLeg
  rw [← Category.assoc, ← T.tensor.map_comp, posetCategorificationTableMap_natural,
    T.tensor.map_comp, Category.assoc, ← Category.assoc (T.tensor.map (complexMap α).nu),
    T.simplex_natural, Category.assoc]
  have hc := congrArg Hom.nu (d.finiteCylinderChainMap_natural σ α)
  change (show (complex P).cylinder.nu ⟶ _ from (d.finiteCylinderChainMap (σ.comp α)).nu) ≫
      (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
        (d.finiteImage_mono σ α))).nu =
      (complexMap α).cylinder.nu ≫ (d.finiteCylinderChainMap σ).nu at hc
  have hcc := congrArg (fun z : (complex P).cylinder.nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫ z ≫
      (d.finiteImage σ).lift) hc
  simp only [Category.assoc, FiniteVertexChain.lift_natural] at hcc
  exact hcc.symm

def prismCocone : Cocone (posetSimplexDiagram E ⋙ T.tensor) where
  pt := categorification.obj (nerve E)
  ι.app s := d.prismLeg T (simplexVertexOrder s)
  ι.naturality s t α := by
    change T.tensor.map (categorification.map (nerveMap (simplexVertexMap α).monotone.functor)) ≫
      d.prismLeg T (simplexVertexOrder t) = d.prismLeg T (simplexVertexOrder s) ≫ 𝟙 _
    rw [d.prismLeg_natural, simplexVertexOrder_natural, Category.comp_id]

def prism : T.tensor.obj (categorification.obj (nerve E)) ⟶ categorification.obj (nerve E) := by
  letI := T.cocontinuous
  letI : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).desc (d.prismCocone T)

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison

lemma finitePosetMap_id (n : ℕ) (E : Type u) [PartialOrder E] :
    posetMap n (OrderHom.id : E →o E) = 𝟙 (posetObj n E) :=
  (categorificationFinite n).map_id (nerve E)

lemma finitePosetMap_comp (n : ℕ) {P Q R : Type u} [PartialOrder P]
    [PartialOrder Q] [PartialOrder R] (f : P →o Q) (g : Q →o R) :
    posetMap n (g.comp f) = posetMap n f ≫ posetMap n g :=
  (categorificationFinite n).map_comp (nerveMap f.toFunctor) (nerveMap g.toFunctor)

end Thomason.GreatestNew

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


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory

lemma weak_of_full_sieve_cover {C : OmegaCategory.{u}} {S T : Set C.Objects}
    (hS : C.IsObjectSieve S) (hT : C.IsObjectSieve T)
    (hc : S ∪ T = Set.univ) {X : SSet.{u}} (j : X ⟶ streetNerve C)
    (jS : X ⟶ streetNerve (C.fullOn S).category)
    (jT : X ⟶ streetNerve (C.fullOn T).category)
    (jI : X ⟶ streetNerve (C.fullOn (S ∩ T)).category)
    (heS : jS ≫ streetNerveMap (C.fullOn S).inclusion = j)
    (heT : jT ≫ streetNerveMap (C.fullOn T).inclusion = j)
    (heI : jI ≫ streetNerveMap (C.fullOn (S ∩ T)).inclusion = j)
    (hwS : simplicialWeakEquivalences jS)
    (hwT : simplicialWeakEquivalences jT)
    (hwI : simplicialWeakEquivalences jI) : simplicialWeakEquivalences j := by
  let pS := streetNerveMap (fullOnMap (Set.inter_subset_left (s := S) (t := T)))
  let pT := streetNerveMap (fullOnMap (Set.inter_subset_right (s := S) (t := T)))
  have he : jI ≫ pS = jS := by
    apply (cancel_mono (streetNerveMap (C.fullOn S).inclusion)).mp
    rw [Category.assoc, heS]
    exact heI
  have hw : simplicialWeakEquivalences pS :=
    simplicialWeakEquivalences.of_precomp jI pS hwI (he ▸ hwS)
  have sq := sieve_cover_nerve_isPushout hS hT (fun a => by
    have ha : a ∈ S ∪ T := by rw [hc]; trivial
    exact ha)
  have hwT' : simplicialWeakEquivalences (streetNerveMap (C.fullOn T).inclusion) :=
    GeometricRecognition.left_proper _ _ _ _ sq.flip (by infer_instance) hw
  rw [← heT]
  exact simplicialWeakEquivalences.comp_mem _ _ hwT hwT'

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma finite_nerve_attachment_mono (n : ℕ) (hn : 1 ≤ n)
    {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n B ⟶ Y) (sc : IsPushout a (inc n A) j v) :
    Mono ((streetNerveFinite n).map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_finite_sieve_attachment n hn A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.val.fullOn S)
  have hj : Mono ((nCategoryInclusion n).map j) := by
    change @Mono OmegaCategory inferInstance X.val Y.val j
    rw [← he]
    infer_instance
  have : Mono j := (nCategoryInclusion n).mono_of_mono_map hj
  let : PreservesLimits (streetNerveFinite n) :=
    (categorificationFiniteAdjunction n).rightAdjoint_preservesLimits
  infer_instance

end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z


namespace Thomason.FilteredWeak
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open KanPath LastVertexProof KanHomotopy HornSubdivision SSet.modelCategoryQuillen

theorem kan_colimit_weak {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hX : ∀ j, SSet.KanComplex (X.obj j)) (hY : ∀ j, SSet.KanComplex (Y.obj j))
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences (colim.map p) := by
  have hproj : simplicialWeakEquivalences (colim.map (pathProjection p)) := by
    apply KanQuillen.boundary_right_weak
    apply boundary_rlp_colimit
    intro j
    let := hY j
    exact path_projection_rlp (p.app j)
  have hr : simplicialWeakEquivalences (colim.map (pathRight p)) := by
    apply KanQuillen.boundary_right_weak
    apply boundary_rlp_colimit
    intro j
    let := hX j
    let := hY j
    rw [← SSet.rlp_monomorphisms]
    exact right_rlp (p.app j) (GeometricRecognition.weak_kan_heq _ (hp j))
  have hl : simplicialWeakEquivalences (colim.map (pathLeft p)) := by
    apply simplicialWeakEquivalences.of_postcomp _ _ hproj
    rw [← CategoryTheory.Functor.map_comp,path_left_projection,CategoryTheory.Functor.map_id]
    exact simplicialWeakEquivalences.id_mem _
  simpa only [← CategoryTheory.Functor.map_comp,path_fac] using simplicialWeakEquivalences.comp_mem _ _ hl hr

theorem colimit_weak {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences (colim.map p) := by
  let R := Subdivision.exInfinityFunctor.{u}
  have hr : simplicialWeakEquivalences (colim.map (CategoryTheory.Functor.whiskerRight p R)) :=
    kan_colimit_weak (CategoryTheory.Functor.whiskerRight p R)
      (fun j => Subdivision.exInfinity_kan (X.obj j))
      (fun j => Subdivision.exInfinity_kan (Y.obj j))
      (fun j => (Subdivision.exInfinity_map_weak_iff (p.app j)).mpr (hp j))
  apply (Subdivision.exInfinity_map_weak_iff (colim.map p)).mp
  apply simplicialWeakEquivalences.of_postcomp _ (preservesColimitIso R Y).hom
    (simplicialWeakEquivalences.of_isIso _)
  have hw : R.map (colim.map p) ≫ (preservesColimitIso R Y).hom =
      (preservesColimitIso R X).hom ≫ colim.map (CategoryTheory.Functor.whiskerRight p R) :=
    (preservesColimitNatIso R).hom.naturality p
  rw [hw]
  exact simplicialWeakEquivalences.comp_mem _ _ (simplicialWeakEquivalences.of_isIso _) hr

lemma weak_of_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) (c : Cocone X) (d : Cocone Y)
    (hc : IsColimit c) (hd : IsColimit d) (f : c.pt ⟶ d.pt)
    (fac : ∀ j, c.ι.app j ≫ f = p.app j ≫ d.ι.app j)
    (hp : ∀ j, simplicialWeakEquivalences (p.app j)) :
    simplicialWeakEquivalences f := by
  let e₁ := hc.coconePointUniqueUpToIso (colimit.isColimit X)
  let e₂ := (colimit.isColimit Y).coconePointUniqueUpToIso hd
  have h₁ (j : J) : c.ι.app j ≫ e₁.hom = colimit.ι X j :=
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X) j
  have h₂ (j : J) : colimit.ι Y j ≫ e₂.hom = d.ι.app j :=
    (colimit.isColimit Y).comp_coconePointUniqueUpToIso_hom hd j
  have he : f = e₁.hom ≫ colim.map p ≫ e₂.hom := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc,← Category.assoc,h₁,colimit.ι_map,Category.assoc,h₂]
    exact fac j
  rw [he]
  exact simplicialWeakEquivalences.comp_mem _ _ (simplicialWeakEquivalences.of_isIso _)
    (simplicialWeakEquivalences.comp_mem _ _ (colimit_weak p hp)
      (simplicialWeakEquivalences.of_isIso _))

end Thomason.FilteredWeak

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AttachmentComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits FilteredPosets FilteredPushouts

theorem couniversal_of_finite {D : Type v} [Category.{w} D] [HasPushouts D]
    (L : SSet.{u} ⥤ D) (N : D ⥤ SSet.{u}) [PreservesColimitsOfSize.{u,u} L]
    (hfin : ∀ (P : Type u) [PartialOrder P] [Finite P] (A : Set P),
      IsLowerSet A → ∀ (r : P →o A), (∀ (a : A) (x : P), a.val ≤ x ↔ a ≤ r x) →
      ∀ {X Y : D} (a : L.obj (nerve A) ⟶ X) (j : X ⟶ Y) (v : L.obj (nerve P) ⟶ Y),
        IsPushout a (L.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v →
          simplicialWeakEquivalences (N.map j))
    {E : Type u} [PartialOrder E] [PreservesColimitsOfShape (Finset E) N]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : D} (a : L.obj (nerve A) ⟶ X) (j : X ⟶ Y) (v : L.obj (nerve E) ⟶ Y)
    (sq : IsPushout a (L.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v) :
    simplicialWeakEquivalences (N.map j) := by
  classical
  let q : E → E := fun e => (r e).val
  have hr (x : A) : r x.val = x :=
    le_antisymm ((hadj (r x.val) x.val).mpr le_rfl) ((hadj x x.val).mp le_rfl)
  have hq (x : E) : q (q x) = q x := congrArg Subtype.val (hr (r x))
  let S := closedFamily q
  let cA := L.mapCocone (PartOrd.nerveFunctor.mapCocone (oldCocone S A))
  let cB := L.mapCocone (PartOrd.nerveFunctor.mapCocone (cocone S))
  have hcA : IsColimit cA := isColimitOfPreserves L
    (oldUnionIsColimit S (closedFamily_cover q) A)
  have hcB : IsColimit cB := isColimitOfPreserves L
    (unionIsColimit S (closedFamily_cover q))
  let b := CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerRight (inclusion S A) PartOrd.nerveFunctor) L
  let b₀ := L.map (nerveMap (OrderEmbedding.subtype (fun element : E => element ∈ A)).toOrderHom.toFunctor)
  have hb : b ≫ cB.ι = cA.ι ≫ (CategoryTheory.Functor.const (Finset E)).map b₀ := by
    apply NatTrans.ext
    funext s
    change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
    erw [← L.map_comp,← L.map_comp]
    rfl
  let cY := attachmentCocone cA cB a b b₀ hb j v sq
  have hcY : IsColimit cY := attachmentIsColimit cA cB hcA hcB a b b₀ hb j v sq
  let p := pushout.inl (attachingMap cA a) b
  let cp := constCocone (Finset E) X
  have hp (s : Finset E) : simplicialWeakEquivalences (N.map (p.app s)) := by
    let r' : S s →o {x : S s | x.val ∈ A} :=
      ⟨fun x => ⟨⟨(r x.val).val, close_stable q hq s x.property⟩,(r x.val).property⟩,
        fun _ _ h => r.monotone h⟩
    apply hfin (S s) {x : S s | x.val ∈ A} (restricted_lower hA (S s)) r'
      (fun x y => hadj ⟨x.val.val,x.property⟩ y.val) ((attachingMap cA a).app s)
      (p.app s) ((pushout.inr (attachingMap cA a) b).app s)
    exact (IsPushout.of_hasPushout (attachingMap cA a) b).map
      ((evaluation (Finset E) D).obj s)
  apply FilteredWeak.weak_of_colimit (CategoryTheory.Functor.whiskerRight p N)
    (N.mapCocone cp) (N.mapCocone cY)
    (isColimitOfPreserves N (isColimitConstCocone (Finset E) X))
    (isColimitOfPreserves N hcY) (N.map j) _ hp
  intro s
  change N.map (𝟙 X) ≫ N.map j = N.map (p.app s) ≫ N.map (cY.ι.app s)
  rw [N.map_id,Category.id_comp,← N.map_comp]
  exact congrArg (fun f : X ⟶ Y => N.map f)
    (attachmentCocone_inl cA cB a b b₀ hb j v sq s).symm

end Thomason.Couniversality

end

end OAI
end


