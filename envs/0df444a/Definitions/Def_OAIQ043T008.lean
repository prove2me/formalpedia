-- Prove2me | Definitions.Def_OAIQ043T008
-- name    : OAIQ043T008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T10:03:21.232556+00:00
-- url     : https://prove2.me/theorems/8b630795-4c44-4c70-affa-70454bc3356b
-- title:
--   Definitions bundle OAIQ043T008 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 165 declarations of OpenAI's Lean: 27 definitions, 3 inductive types or structures and 135 theorems. The definitions and types are `OAI.Thomason.DirectedComplex.PartialHom.ofHom`, `OAI.Thomason.DirectedComplex.PositiveAcyclic`, `OAI.Thomason.GrayRecursive.RectangleCell`, `OAI.Thomason.GrayRecursive.RectangleCell.eval`, `OAI.Thomason.GrayRecursive.RectangleCell.truncate`, `OAI.Thomason.GrayRecursive.RectangleDiagram`, `OAI.Thomason.GrayRecursive.RectangleDiagram.cellMap`, `OAI.Thomason.GrayRecursive.RectangleDiagram.interpret`, `OAI.Thomason.GrayRecursive.RectangleDiagram.lift`, `OAI.Thomason.GrayRecursive.extractDiagonal`, `OAI.Thomason.GrayRecursive.intervalLabel`, `OAI.Thomason.GrayRecursive.rectangleDiagramOfFunctor`, `OAI.Thomason.GrayRecursive.rectangleEquiv`, `OAI.Thomason.GreatestNew.omegaInc`, `OAI.Thomason.GreatestNew.omegaPosetMap`, `OAI.Thomason.GreatestNew.omegaPosetObj`, `OAI.Thomason.OmegaAttachmentComparison.inc`, `OAI.Thomason.OmegaAttachmentComparison.sb`, `OAI.Thomason.OmegaCategory.Functor.homMap`, `OAI.Thomason.OmegaCategory.homCategory`, `OAI.Thomason.RelativePrismData.finitePrism`, `OAI.Thomason.RightIntervalExtension.finiteGlue`, `OAI.Thomason.RightIntervalExtension.finiteInternalHom`, `OAI.Thomason.RightIntervalExtension.finiteTranspose`, `OAI.Thomason.RightIntervalExtension.nerveCylinder`, `OAI.Thomason.RightIntervalExtension.nerveCylinderSimplex`, `OAI.Thomason.RightIntervalExtension.nerveHomotopy`, `OAI.Thomason.RightIntervalExtension.omegaGlue`, `OAI.Thomason.RightIntervalExtension.raiseSimplex`, `OAI.Thomason.RightIntervalExtension.truncatedCylinderEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: [`Thomason_AttachmentComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/AttachmentComparison.lean), [`Thomason_Couniversality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/Couniversality.lean), [`Thomason_CylinderProfiles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/CylinderProfiles.lean), [`Thomason_FiniteAttachments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/FiniteAttachments.lean), [`Thomason_GlobularGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/GlobularGeneration.lean), [`Thomason_GreatestAttachments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/GreatestAttachments.lean), [`Thomason_IntervalExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/IntervalExtension.lean), [`Thomason_PartialPrisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PartialPrisms.lean), [`Thomason_ProperTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/ProperTransfer.lean), [`Thomason_RectangleComposition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/RectangleComposition.lean), [`Thomason_RecursiveCylinders`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/RecursiveCylinders.lean), [`Thomason_SieveAttachments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/SieveAttachments.lean).
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T006` and `OAIQ043T007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T010` and `OAIQ043T011`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T006
import Definitions.Def_OAIQ043T007

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
open Table OmegaCategory
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def ofHom (f : Hom K L) (n : ℕ) : PartialHom K L n where
  map := f.map
  map_d p _ x := f.map_d p x
  map_augmentation := f.map_augmentation
  map_positive := f.map_positive

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

lemma constantAttachmentLabel_old :
    h ≫ constantAttachmentLabel A l b hlA a h i H = constantLabel X b := H.inl_desc _ _ _
lemma constantAttachmentLabel_new :
    i ≫ constantAttachmentLabel A l b hlA a h i H = posetCategorificationLabel l := H.inr_desc _ _ _

lemma constant_attachment_old_piece (S : Set P) (hAS : A ⊆ S)
    (hS : S = {p | l p = b}) :
    IsPosetAttachmentPiece A S hAS a h i
      (intervalFiberObjects (constantAttachmentLabel A l b hlA a h i H) b) := by
  let η := constantAttachmentLabel A l b hlA a h i H
  let q := posetCategorificationLabel l
  let C := categorification.obj (nerve A)
  let g : C ⟶ categorification.obj (nerve P) :=
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over interval := Over.mk (constantLabel C b)
  let old : Over interval := Over.mk (constantLabel X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetCategorificationLabel_natural _ l).trans (posetLabel_constant _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantAttachmentLabel_old A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantAttachmentLabel_new A l b hlA a h i H)
  let F := fiberFunctor (intervalVertex b)
  let E := posetPieceFiberIso S l b hS
  let j := (constantFiberIso X b).hom ≫ F.map hf
  let k := E.hom ≫ F.map if'
  have := (q.fiber (intervalVertex b)).inclusion_mono
  have hE := posetPieceFiberIso_inclusion S l b hS
  have hp : IsPushout a
      (categorification.map (nerveMap (subposetMap A S hAS).monotone.functor)) j k := by
    refine (labelled_pushout_fibers af gf hf if' H b).of_iso'
      (constantFiberIso C b) (constantFiberIso X b) E (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · apply (cancel_mono (C := OmegaCategory.{u})
        (q.fiber (intervalVertex b)).inclusion).mp
      change g = categorification.map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
        (E.hom ≫ (q.fiber (intervalVertex b)).inclusion)
      rw [hE]
      exact (subposetMap_comp A S hAS).symm
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
  let Efull := intervalFiberFullIso η b
  refine ⟨j ≫ Efull.hom,k ≫ Efull.hom,?_,?_,?_⟩
  · rfl
  · change k ≫ (η.fiber (intervalVertex b)).inclusion = _
    change E.hom ≫ (F.map if' ≫ (η.fiber (intervalVertex b)).inclusion) = _
    change E.hom ≫ ((q.fiber (intervalVertex b)).inclusion ≫ i) = _
    rw [← Category.assoc, hE]
  · exact hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) Efull
      (by simp) (by simp) (by simp) (by simp)

lemma constant_attachment_new_piece (S : Set P) (e : Fin 2) (hbe : b ≠ e)
    (hS : S = {p | l p = e}) :
    IsPosetNewPiece S i (intervalFiberObjects (constantAttachmentLabel A l b hlA a h i H) e) := by
  let η := constantAttachmentLabel A l b hlA a h i H
  let q := posetCategorificationLabel l
  let C := categorification.obj (nerve A)
  let g : C ⟶ categorification.obj (nerve P) :=
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over interval := Over.mk (constantLabel C b)
  let old : Over interval := Over.mk (constantLabel X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetCategorificationLabel_natural _ l).trans (posetLabel_constant _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantAttachmentLabel_old A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantAttachmentLabel_new A l b hlA a h i H)
  let F := fiberFunctor (intervalVertex e)
  have : IsEmpty (F.obj src).Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsEmpty (F.obj old).Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsIso (F.map af) := isIso_of_isInitial
    (emptyOmegaIsInitial (F.obj src)) (emptyOmegaIsInitial (F.obj old)) _
  have hp := labelled_pushout_fibers af gf hf if' H e
  have : IsIso (F.map if') := hp.isIso_inr_of_isIso
  let E := posetPieceFiberIso S l e hS
  let fiberIso := asIso (F.map if')
  refine ⟨E ≪≫ fiberIso ≪≫ intervalFiberFullIso η e, ?_⟩
  change E.hom ≫ (F.map if' ≫ (η.fiber (intervalVertex e)).inclusion) = _
  change E.hom ≫ ((q.fiber (intervalVertex e)).inclusion ≫ i) = _
  rw [← Category.assoc, posetPieceFiberIso_inclusion]

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

theorem sieve_attachment_covers {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsLowerSet S₁) (h₂ : IsLowerSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : A ⊆ S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.Objects,
      Y.IsObjectSieve T₁ ∧ Y.IsObjectSieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetAttachmentPiece A S₁ hA₁ a h i T₁ ∧
      IsPosetAttachmentPiece A S₂ hA₂ a h i T₂ ∧
      IsPosetAttachmentPiece A (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩)
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
  let η₁ := constantAttachmentLabel A l₁ 0 hl₁ a h i H
  let η₂ := constantAttachmentLabel A l₂ 0 hl₂ a h i H
  let η₃ := constantAttachmentLabel A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = maxLabel η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_old,comp_maxLabel,
        constantAttachmentLabel_old,constantAttachmentLabel_old]
      rfl
    · change i ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_new,comp_maxLabel,
        constantAttachmentLabel_new,constantAttachmentLabel_new]
      rfl
  have hp₃ := constant_attachment_old_piece A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩) hS₃
  change IsPosetAttachmentPiece A (S₁ ∩ S₂) _ a h i (intervalFiberObjects η₃ 0) at hp₃
  rw [hη₃,maxLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 0,intervalFiberObjects η₂ 0,
    zero_fiber_isObjectSieve η₁,zero_fiber_isObjectSieve η₂,?_,
    constant_attachment_old_piece A l₁ 0 hl₁ a h i H S₁ hA₁ hS₁,
    constant_attachment_old_piece A l₂ 0 hl₂ a h i H S₂ hA₂ hS₂,hp₃⟩
  refine labelled_objects_cover H η₁ η₂ l₁ l₂ 0
    (Or.inl (constantAttachmentLabel_old A l₁ 0 hl₁ a h i H))
    (constantAttachmentLabel_new A l₁ 0 hl₁ a h i H)
    (constantAttachmentLabel_new A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((lowerSegmentLabel_zero S₁ h₁ p).mpr) ((lowerSegmentLabel_zero S₂ h₂ p).mpr)

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

theorem cosieve_attachment_covers {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsUpperSet S₁) (h₂ : IsUpperSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : Disjoint A S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.Objects,
      Y.IsObjectCosieve T₁ ∧ Y.IsObjectCosieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetAttachmentPiece A S₁ hA₁ a h i T₁ ∧
      IsPosetNewPiece S₂ i T₂ ∧ IsPosetNewPiece (S₁ ∩ S₂) i (T₁ ∩ T₂) :=
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
  let η₁ := constantAttachmentLabel A l₁ 1 hl₁ a h i H
  let η₂ := constantAttachmentLabel A l₂ 0 hl₂ a h i H
  let η₃ := constantAttachmentLabel A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = minLabel η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_old,comp_minLabel,
        constantAttachmentLabel_old,constantAttachmentLabel_old]
      rfl
    · change i ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_new,comp_minLabel,
        constantAttachmentLabel_new,constantAttachmentLabel_new]
      rfl
  have hp₃ := constant_attachment_new_piece A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) 1 (by decide) hS₃
  change IsPosetNewPiece (S₁ ∩ S₂) i (intervalFiberObjects η₃ 1) at hp₃
  rw [hη₃,minLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 1,intervalFiberObjects η₂ 1,
    one_fiber_isObjectCosieve η₁,one_fiber_isObjectCosieve η₂,?_,
    constant_attachment_old_piece A l₁ 1 hl₁ a h i H S₁ hA₁ hS₁,
    constant_attachment_new_piece A l₂ 0 hl₂ a h i H S₂ 1 (by decide) hS₂,hp₃⟩
  refine labelled_objects_cover H η₁ η₂ l₁ l₂ 1
    (Or.inl (constantAttachmentLabel_old A l₁ 1 hl₁ a h i H))
    (constantAttachmentLabel_new A l₁ 1 hl₁ a h i H)
    (constantAttachmentLabel_new A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((upperSegmentLabel_one S₁ h₁ p).mpr) ((upperSegmentLabel_one S₂ h₂ p).mpr)

end Thomason.Attachments

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


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

lemma downRow_upRow (n p : ℕ) (x : (K.{u} n).Chain p) : downRow n p (upRow n p x) = x := by
  cases p <;> rfl

lemma upRow_downRow_succ (n p : ℕ) (x : (K.{u} (n+1)).Chain (p+2)) :
    upRow n (p+1) (downRow n (p+1) x) = x := by
  rfl

lemma upRow_downRow_zero {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) (b : Bool) :
    upRow n 0 (downRow n 0 (t.row 1 b)) = t.row 1 b := by
  exact Prod.ext rfl (Prod.ext rfl (diagonal_row_one t ht b).2.symm)

lemma up_down {n : ℕ} (t : Table (K.{u} (n+1))) (ht : IsDiagonal t) : up (down t ht) = t := by
  ext p b
  cases p with
  | zero => exact (ht b).symm
  | succ p =>
    change upRow n p (downRow n p (t.row (p+1) b)) = t.row (p+1) b
    cases p with
    | zero => exact upRow_downRow_zero t ht b
    | succ p => exact upRow_downRow_succ n p (t.row (p+2) b)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def homCategory (C : OmegaCategory.{u}) (a b : C.Cell) : OmegaCategory.{u} where
  Cell := {x : C.Cell // C.source 0 x = a ∧ C.target 0 x = b}
  source k x := ⟨C.source (k+1) x.val, by
    simpa only [C.source_source, C.target_source, Nat.zero_min, Nat.zero_lt_succ,
      ite_true] using x.property⟩
  target k x := ⟨C.target (k+1) x.val, by
    simpa only [C.source_target, C.target_target, Nat.zero_min, Nat.zero_lt_succ,
      ite_true] using x.property⟩
  source_source i j x := Subtype.ext (by
    change C.source (i+1) (C.source (j+1) x.val) = C.source (min i j + 1) x.val
    rw [C.source_source, Nat.add_min_add_right])
  target_target i j x := Subtype.ext (by
    change C.target (i+1) (C.target (j+1) x.val) = C.target (min i j + 1) x.val
    rw [C.target_target, Nat.add_min_add_right])
  source_target i j x := by
    apply Subtype.ext
    by_cases h : i < j
    · simp only [h, ite_true]
      exact (C.source_target (i+1) (j+1) x.val).trans (ite_eq_left (by omega))
    · simp only [h, ite_false]
      exact (C.source_target (i+1) (j+1) x.val).trans (ite_eq_right (by omega))
  target_source i j x := by
    apply Subtype.ext
    by_cases h : i < j
    · simp only [h, ite_true]
      exact (C.target_source (i+1) (j+1) x.val).trans (ite_eq_left (by omega))
    · simp only [h, ite_false]
      exact (C.target_source (i+1) (j+1) x.val).trans (ite_eq_right (by omega))
  comp k x y h := ⟨C.comp (k+1) x.val y.val (congrArg Subtype.val h), by
    constructor
    · rw [C.source_comp_le 0 (k+1) (by omega)]
      exact x.property.1
    · rw [C.target_comp_le 0 (k+1) (by omega)]
      exact y.property.2⟩
  source_comp_le i k h x y e :=
    Subtype.ext (C.source_comp_le (i+1) (k+1) (by omega) x.val y.val (congrArg Subtype.val e))
  target_comp_le i k h x y e :=
    Subtype.ext (C.target_comp_le (i+1) (k+1) (by omega) x.val y.val (congrArg Subtype.val e))
  source_comp_gt i k h x y e es :=
    Subtype.ext (C.source_comp_gt (i+1) (k+1) (by omega) x.val y.val
      (congrArg Subtype.val e) (congrArg Subtype.val es))
  target_comp_gt i k h x y e et :=
    Subtype.ext (C.target_comp_gt (i+1) (k+1) (by omega) x.val y.val
      (congrArg Subtype.val e) (congrArg Subtype.val et))
  unit_left k x h := Subtype.ext (C.unit_left (k+1) x.val (congrArg Subtype.val h))
  unit_right k x h := Subtype.ext (C.unit_right (k+1) x.val (congrArg Subtype.val h))
  assoc k x y z hxy hyz hxy_z hx_yz :=
    Subtype.ext (C.assoc (k+1) x.val y.val z.val (congrArg Subtype.val hxy)
      (congrArg Subtype.val hyz) (congrArg Subtype.val hxy_z) (congrArg Subtype.val hx_yz))
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    Subtype.ext (C.interchange (k+1) (l+1) (by omega) a.val b.val c.val d.val
      (congrArg Subtype.val hab) (congrArg Subtype.val hcd) (congrArg Subtype.val hac)
      (congrArg Subtype.val hbd) (congrArg Subtype.val hab_cd) (congrArg Subtype.val hac_bd))
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x.val
    exact ⟨k, Subtype.ext (C.source_fixed_upwards (by omega : k ≤ k+1) hk)⟩

namespace Functor
variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

def homMap (F : Functor C D) (a b : C.Cell) :
    Functor (C.homCategory a b) (D.homCategory (F.map a) (F.map b)) where
  map x := ⟨F.map x.val, by
    rw [← F.map_source, ← F.map_target, x.property.1, x.property.2]
    exact ⟨rfl, rfl⟩⟩
  map_source k x := Subtype.ext (F.map_source (k+1) x.val)
  map_target k x := Subtype.ext (F.map_target (k+1) x.val)
  map_comp k x y h h' :=
    Subtype.ext (F.map_comp (k+1) x.val y.val (congrArg Subtype.val h) (congrArg Subtype.val h'))

end Functor

end Thomason.OmegaCategory

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


namespace Thomason.GlobeComplex

lemma positive_cycle_zero {n p : ℕ} (x : Chain.{u} n (p+1))
    (hx : x ∈ (complex n).positive (p+1)) (hd : (complex n).d p x = 0) : x = 0 := by
  apply (mass_eq_zero_iff hx).mp
  have h := congrArg (fun y : Chain n p => y.val ⟨false⟩) hd
  erw [complex_d_coordinate] at h
  change -mass n (p+1) x = 0 at h
  simpa using h

lemma positive_add_zero {n p : ℕ} {x y : Chain.{u} n p}
    (hx : x ∈ (complex n).positive p) (hy : y ∈ (complex n).positive p)
    (h : x+y = 0) : x = 0 ∧ y = 0 := by
  have hm := congrArg (mass n p) h
  rw [map_add, map_zero] at hm
  have hx' := mass_nonneg hx
  have hy' := mass_nonneg hy
  exact ⟨(mass_eq_zero_iff hx).mp (by omega), (mass_eq_zero_iff hy).mp (by omega)⟩

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

lemma cross_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (crossRow t (p+1) b) = crossRow t p true - crossRow t p false :=
  congrArg (fun x : (K n).Chain (p+1) => x.2.2) (t.boundary (p+1) b)

lemma left_boundary {n : ℕ} (t : Table (K.{u} n)) (p : ℕ) (b : Bool) :
    (complex n).d p (sideRow t false (p+1) b) - (-1 : ℤ)^p • crossRow t p b =
      sideRow t false p true - sideRow t false p false := by
  cases p with
  | zero => simpa [sideRow, crossRow, cylinderDifferential] using congrArg Prod.fst (t.boundary 0 b)
  | succ p => exact congrArg Prod.fst (t.boundary (p+1) b)

lemma cross_succ_eq_zero_of_constant {n : ℕ} (t : Table (K.{u} n))
    (h : crossRow t 0 true = crossRow t 0 false) (p : ℕ) (b : Bool) :
    crossRow t (p+1) b = 0 := by
  induction p generalizing b with
  | zero => exact positive_cycle_zero _ (cross_positive t 1 b) (by rw [cross_boundary, h, sub_self])
  | succ p ih =>
    exact positive_cycle_zero _ (cross_positive t (p+2) b)
      (by rw [cross_boundary, ih true, ih false, sub_self])

lemma no_cross_of_stationary_interval {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) = mass n 0 (sideRow t true 0 false)) :
    ∀ p b, crossRow t p b = 0 := by
  have h₀ : ∀ b, crossRow t 0 b = 0 := fun b =>
    (mass_eq_zero_iff (cross_positive t 0 b)).mp (by rw [cross_mass_vertex, h, sub_self])
  intro p b
  cases p with
  | zero => exact h₀ b
  | succ p => exact cross_succ_eq_zero_of_constant t (by rw [h₀ true, h₀ false]) p b

lemma no_side_of_empty_vertex {n : ℕ} (t : Table (K.{u} n)) (a : Bool)
    (h : ∀ p b, crossRow t p b = 0) (h₀ : ∀ b, sideRow t a 0 b = 0) :
    ∀ p b, sideRow t a p b = 0 := by
  intro p b
  induction p generalizing b with
  | zero => exact h₀ b
  | succ p ih =>
    apply positive_cycle_zero _ (side_positive t a (p+1) b)
    cases a with
    | false => simpa only [h, smul_zero, ih, sub_zero, sub_self] using left_boundary t p b
    | true => simpa only [h, smul_zero, ih, add_zero, sub_self] using right_boundary t p b

lemma endpoint_of_stationary_interval {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) = mass n 0 (sideRow t true 0 false)) :
    ∃ a, t = ((complex n).cylinderEndpoint a).table (project t) := by
  have hc := no_cross_of_stationary_interval t h
  rcases side_mass_vertex t true false with h₀ | h₁
  · have hs : ∀ p b, sideRow t true p b = 0 := by
      apply no_side_of_empty_vertex t true hc
      intro b
      apply (mass_eq_zero_iff (side_positive t true 0 b)).mp
      cases b
      · exact h₀
      · exact h.trans h₀
    refine ⟨false, ?_⟩
    ext p b
    change t.row p b = (complex n).cylinderEndpointMap false p ((project t).row p b)
    rw [project_row, hs p b, add_zero]
    cases p with
    | zero => exact Prod.ext rfl (hs 0 b)
    | succ p => exact Prod.ext rfl (Prod.ext (hs (p+1) b) (hc p b))
  · have hs : ∀ p b, sideRow t false p b = 0 := by
      apply no_side_of_empty_vertex t false hc
      intro b
      apply (mass_eq_zero_iff (side_positive t false 0 b)).mp
      have hh := side_augmentation t b
      cases b <;> omega
    refine ⟨true, ?_⟩
    ext p b
    change t.row p b = (complex n).cylinderEndpointMap true p ((project t).row p b)
    rw [project_row, hs p b, zero_add]
    cases p with
    | zero => exact Prod.ext (hs 0 b) rfl
    | succ p => exact Prod.ext (hs (p+1) b) (Prod.ext rfl (hc p b))

lemma crossing_vertical {n : ℕ} (t : Table (K.{u} n))
    (h : mass n 0 (sideRow t true 0 true) ≠ mass n 0 (sideRow t true 0 false))
    (hpj : truncate 0 false (project t) = project t) : t = verticalTable (project t) := by
  have hz : ∀ p b, (project t).row (p+1) b = 0 := by
    intro p b
    rw [← hpj, truncate_row]
    simp
  have hs : ∀ p b, sideRow t false (p+1) b = 0 ∧ sideRow t true (p+1) b = 0 := by
    intro p b
    exact positive_add_zero (side_positive t false (p+1) b) (side_positive t true (p+1) b)
      (by erw [← project_row, hz]; rfl)
  have he : ∀ b, (project t).row 0 b = (project t).row 0 true := by
    intro b
    have h₀ := congrArg (fun x : Table (complex n) => x.row 0 b) hpj
    have h₁ := congrArg (fun x : Table (complex n) => x.row 0 true) hpj
    exact h₀.symm.trans h₁
  have hv := crossing_vertices t h
  obtain ⟨hb, ht⟩ := crossing_sides t h
  have hc₀ : ∀ b, crossRow t 0 b = (project t).row 0 true := by
    intro b
    have hh := right_boundary t 0 b
    rw [(hs 0 b).2, map_zero, zero_add, pow_zero, one_smul, hb, sub_zero, hv true] at hh
    exact hh
  have hc : ∀ p b, crossRow t (p+1) b = 0 :=
    cross_succ_eq_zero_of_constant t (by rw [hc₀, hc₀])
  ext p b
  cases p with
  | zero =>
    change t.row 0 b = verticalRow (project t) 0 b
    cases b
    · exact Prod.ext (hv false) hb
    · exact Prod.ext ht (hv true)
  | succ p =>
    cases p with
    | zero =>
      change t.row 1 b = verticalRow (project t) 1 b
      simp only [verticalRow, show ¬Even (1 : ℕ) by decide, ite_false, hz]
      cases b <;> exact Prod.ext (hs 0 _).1 (Prod.ext (hs 0 _).2 ((hc₀ _).trans (he _).symm))
    | succ p =>
      change t.row (p+2) b = verticalRow (project t) (p+2) b
      simp only [verticalRow, hz]
      split_ifs <;> cases b <;> exact Prod.ext (hs (p+1) _).1 (Prod.ext (hs (p+1) _).2 (hc p _))

lemma table_cases {n : ℕ} (t : Table (K.{u} (n+1))) :
    (∃ a, t = ((complex (n+1)).cylinderEndpoint a).table (project t)) ∨
    (∃ a, t = verticalTable (truncate 0 a (topTable (n+1)))) ∨ IsDiagonal t := by
  by_cases h : mass (n+1) 0 (sideRow t true 0 true) = mass (n+1) 0 (sideRow t true 0 false)
  · exact Or.inl (endpoint_of_stationary_interval t h)
  · obtain ⟨p, a, _, hpj⟩ := table_classification (project t)
    cases p with
    | zero =>
      right; left
      refine ⟨a, ?_⟩
      rw [crossing_vertical t h (by rw [hpj]; simp [truncate_truncate]), hpj]
    | succ p => exact Or.inr (Or.inr (crossing_diagonal t h (by omega) a hpj))

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open DirectedComplex DirectedComplex.Table

lemma suspendTable_top (n : ℕ) : suspendTable (topTable.{u} n) = topTable (n+1) := by
  ext p b
  cases p with
  | zero => exact (topRow_lt (n+1) 0 b (by omega)).symm
  | succ p =>
    change (shiftDown n p).symm (topRow n p b) = topRow (n+1) (p+1) b
    by_cases hp : p < n
    · rw [topRow_lt _ _ _ hp, topRow_lt _ _ _ (by omega)]
      rfl
    · by_cases hn : p = n
      · subst p
        rw [topRow_eq, topRow_eq]
        rfl
      · erw [topRow_gt _ _ _ (by omega), topRow_gt _ _ _ (by omega), map_zero]
        rfl

lemma suspendTable_eq_face {n k : ℕ} (b : Bool) :
    suspendTable (truncate k b (topTable.{u} n)) = truncate (k+1) b (topTable (n+1)) := by
  rw [suspendTable_truncate, suspendTable_top]

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

@[simp] lemma vertexWeights_one_zero (n : ℕ) :
    vertexWeights.{u} n 1 0 = basis (n+1) 0 false (Or.inl (by omega)) := by
  apply Subtype.ext
  funext ⟨b⟩
  cases b <;> rfl

@[simp] lemma vertexWeights_zero_one (n : ℕ) :
    vertexWeights.{u} n 0 1 = basis (n+1) 0 true (Or.inl (by omega)) := by
  apply Subtype.ext
  funext ⟨b⟩
  cases b <;> rfl

lemma up_truncate {n : ℕ} (t : Table (K.{u} n)) (k : ℕ) (e : Bool) :
    up (truncate k e t) = truncate (k+1) e (up t) := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [up_succ, truncate_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs <;> simp

lemma up_composable {n k : ℕ} {s t : Table (K.{u} n)}
    (h : truncate k true s = truncate k false t) :
    truncate (k+1) true (up s) = truncate (k+1) false (up t) := by
  rw [← up_truncate, ← up_truncate, h]

lemma up_comp {n k : ℕ} (s t : Table (K.{u} n))
    (h : truncate k true s = truncate k false t)
    (h' : truncate (k+1) true (up s) = truncate (k+1) false (up t)) :
    up (DirectedComplex.Table.comp k s t h) = DirectedComplex.Table.comp (k+1) (up s) (up t) h' := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [up_succ, comp_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs <;> simp

lemma up_endpoint_left_matching {n : ℕ} (x : Table (complex.{u} n)) :
    truncate 0 true (verticalTable (vertex n false)) = truncate 0 false (atEnd true (suspendTable x)) := by
  ext p b
  cases p with
  | zero =>
    simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]
    change (0, (vertex n false).row 0 true) = (0, (suspendTable x).row 0 false)
    simp
  | succ p => simp

lemma up_endpoint_right_matching {n : ℕ} (x : Table (complex.{u} n)) :
    truncate 0 true (atEnd false (suspendTable x)) = truncate 0 false (verticalTable (vertex n true)) := by
  ext p b
  cases p with
  | zero =>
    simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]
    change ((suspendTable x).row 0 true, 0) = ((vertex n true).row 0 false, 0)
    simp
  | succ p => simp

lemma up_endpoint_false {n : ℕ} (x : Table (complex.{u} n)) :
    up (atEnd false x) = DirectedComplex.Table.comp 0 (verticalTable (vertex n false))
      (atEnd true (suspendTable x)) (up_endpoint_left_matching x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;>
        simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
          verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · rfl
        · exact (zero_add _).symm
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      simp only [up_succ, comp_row, Nat.not_lt_zero, ite_false, Nat.succ_ne_zero]
      simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
        verticalTable, verticalRow, upRow]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · rfl
      · exact (zero_add _).symm
      · rfl

lemma up_endpoint_true {n : ℕ} (x : Table (complex.{u} n)) :
    up (atEnd true x) = DirectedComplex.Table.comp 0 (atEnd false (suspendTable x))
      (verticalTable (vertex n true)) (up_endpoint_right_matching x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;>
        simp [comp_row, atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
          verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (add_zero _).symm
        · rfl
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      simp only [up_succ, comp_row, Nat.not_lt_zero, ite_false, Nat.succ_ne_zero]
      simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
        verticalTable, verticalRow, upRow]
      exact Prod.ext (add_zero _).symm rfl

lemma up_vertical {n : ℕ} (x : Table (complex.{u} n)) :
    up (verticalTable x) = verticalTable (suspendTable x) := by
  ext p b
  cases p with
  | zero => cases b <;> simp [verticalTable, verticalRow, diagonalRow]
  | succ p =>
    cases p with
    | zero =>
      cases b <;> simp [verticalTable, verticalRow, upRow, table_mass_zero]
      all_goals
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · rfl
        · rfl
        · apply Subtype.ext
          funext ⟨index⟩
          cases index <;> rfl
    | succ p =>
      by_cases hp : Even (p+1)
      · have hp' : ¬Even (p+1+1) := by rw [Nat.even_add_one]; exact not_not_intro hp
        cases b <;> simp [verticalTable, verticalRow, upRow, hp, hp'] <;> rfl
      · have hp' : Even (p+1+1) := by rw [Nat.even_add_one]; exact hp
        cases b <;> simp [verticalTable, verticalRow, upRow, hp, hp'] <;> rfl

lemma table_zero_cases (t : Table (K.{u} 0)) :
    (∃ a, t = atEnd a (project t)) ∨ t = verticalTable (topTable 0) := by
  by_cases h : mass 0 0 (sideRow t true 0 true) = mass 0 0 (sideRow t true 0 false)
  · exact Or.inl (endpoint_of_stationary_interval t h)
  · right
    obtain ⟨p,a,hp,he⟩ := table_classification (project t)
    have hp0 : p = 0 := by omega
    subst p
    have ht : project t = topTable 0 := by
      rw [he, ← face_nu]
      exact (complex 0).nu.face_of_fixed (topTable_bounded 0) (le_refl 0) a
    rw [crossing_vertical t h (by rw [ht]; exact topTable_bounded 0), ht]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Table
variable {K : DirectedComplex.{u}}

lemma fixed_of_rows_zero {k : ℕ} (x : Table K)
    (h : ∀ p, k < p → ∀ b, x.row p b = 0) : truncate k false x = x := by
  have ht : x.row k true = x.row k false := by
    have hb := x.boundary k false
    rw [h (k+1) (by omega) false, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  ext p b
  rw [truncate_row]
  split_ifs with hp he
  · rfl
  · subst p
    cases b <;> simp [ht]
  · exact (h p (by omega) b).symm

end Thomason.DirectedComplex.Table

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma up_injective (n : ℕ) : Function.Injective (@up.{u} n) := by
  intro s t h
  ext p b
  have hh := congrArg (fun x : Table (K (n+1)) => downRow n p (x.row (p+1) b)) h
  exact (downRow_upRow n p (s.row p b)).symm.trans (hh.trans (downRow_upRow n p (t.row p b)))

lemma up_fixed_iff {n k : ℕ} (t : Table (K.{u} n)) :
    truncate (k+1) false (up t) = up t ↔ truncate k false t = t := by
  rw [← up_truncate]
  exact (up_injective n).eq_iff

lemma vertex_fixed (n : ℕ) (a : Bool) : truncate 0 false (vertex.{u} n a) = vertex n a := by
  simp only [vertex, truncate_truncate, lt_self_iff_false, ite_false]

lemma vertical_fixed {K : DirectedComplex.{u}} {k : ℕ} (t : Table K)
    (h : truncate k false t = t) :
    truncate (k+1) false (verticalTable t) = verticalTable t := by
  apply fixed_of_rows_zero
  rintro (_ | p) hp b
  · omega
  · have hz := row_above_fixed t h (by omega : k < p) b
    have hz' := row_above_fixed t h (by omega : k < p+1) b
    simp [verticalTable, verticalRow, hz, hz']

lemma zero_is_endpoint {n : ℕ} (t : Table (K.{u} n))
    (h : truncate 0 false t = t) : ∃ a, t = atEnd a (project t) := by
  apply endpoint_of_stationary_interval
  have hz : crossRow t 0 false = 0 := congrArg (fun x : (K n).Chain 1 => x.2.2)
    (row_above_fixed t h (by omega : 0 < 1) false)
  have hm := cross_mass_vertex t false
  erw [hz, map_zero] at hm
  exact sub_eq_zero.mp hm.symm

lemma generated_bounded (n k : ℕ) (P : Table (K.{u} n) → Prop)
    (hend : ∀ a x, truncate k false x = x → P (atEnd a x))
    (hvertical : ∀ r, r < k → ∀ x, truncate r false x = x → P (verticalTable x))
    (hcomp : ∀ l s t (h : truncate l true s = truncate l false t),
      P s → P t → P (DirectedComplex.Table.comp l s t h)) :
    ∀ x, truncate k false x = x → P x := by
  induction n generalizing k with
  | zero =>
    intro x hx
    cases k with
    | zero =>
      obtain ⟨a,he⟩ := zero_is_endpoint x hx
      rw [he]
      exact hend a (project x) (project_fixed x hx)
    | succ k =>
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he]; exact hend a (project x) (project_fixed x hx)
      · rw [he]; exact hvertical 0 (by omega) (topTable 0) (topTable_bounded 0)
  | succ n ih =>
    intro x hx
    cases k with
    | zero =>
      obtain ⟨a,he⟩ := zero_is_endpoint x hx
      rw [he]
      exact hend a (project x) (project_fixed x hx)
    | succ k =>
      rcases table_cases x with ⟨a,he⟩ | ⟨a,he⟩ | hd
      · rw [he]; exact hend a (project x) (project_fixed x hx)
      · rw [he]; exact hvertical 0 (by omega) (vertex n a) (vertex_fixed n a)
      · have hdown : truncate k false (down x hd) = down x hd := by
          apply (up_fixed_iff _).mp
          rw [up_down x hd]
          exact hx
        rw [← up_down x hd]
        apply ih k (fun y => P (up y)) ?_ ?_ ?_ (down x hd) hdown
        · intro a y hy
          cases a
          · rw [up_endpoint_false]
            exact hcomp 0 _ _ _ (hvertical 0 (by omega) _ (vertex_fixed _ _))
              (hend true _ (suspend_fixed y hy))
          · rw [up_endpoint_true]
            exact hcomp 0 _ _ _ (hend false _ (suspend_fixed y hy))
              (hvertical 0 (by omega) _ (vertex_fixed _ _))
        · intro r hr y hy
          rw [up_vertical]
          exact hvertical (r+1) (by omega) _ (suspend_fixed y hy)
        · intro l s t h hs ht
          rw [up_comp s t h (up_composable h)]
          exact hcomp (l+1) _ _ _ hs ht

lemma functor_ext_truncated {n k : ℕ} {Y : OmegaCategory.{v}} (hY : Y.IsTruncated k)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y)
    (hend : ∀ a x, truncate k false x = x → F.map (atEnd a x) = G.map (atEnd a x))
    (hvert : ∀ r, r < k → ∀ x, truncate r false x = x →
      F.map (verticalTable x) = G.map (verticalTable x)) : F = G := by
  have hb (x : Table (K n)) (hx : truncate k false x = x) : F.map x = G.map x := by
    apply generated_bounded n k (fun t => F.map t = G.map t) hend hvert ?_ x hx
    intro l s t h hs ht
    have hf := F.map_comp l s t h (by erw [← F.map_target, ← F.map_source]; exact congrArg F.map h)
    have hg := G.map_comp l s t h (by erw [← G.map_target, ← G.map_source]; exact congrArg G.map h)
    exact hf.trans ((Y.comp_congr_cells l _ _ hs ht).trans hg.symm)
  apply OmegaCategory.Functor.ext
  funext x
  have he := hb (truncate k false x) (by erw [truncate_truncate, ite_self])
  change F.map ((K n).nu.source k x) = G.map ((K n).nu.source k x) at he
  rw [F.map_source, G.map_source, hY, hY] at he
  exact he

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


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma sourceCollapse_cylinder_truncated {i k : ℕ} {Y : OmegaCategory.{v}}
    (hk : Y.IsTruncated k) (F : OmegaCategory.Functor (K.{u} i).nu Y) :
    OmegaCategory.Functor.comp (sourceCollapse i k).cylinder.nu F = F := by
  apply functor_ext_truncated hk
  · intro a x _
    change F.map ((sourceCollapse i k).cylinder.nu.map (atEnd a x)) = F.map (atEnd a x)
    rw [cylinder_map_endpoint]
    let E : OmegaCategory.Functor (complex i).nu Y :=
      OmegaCategory.Functor.comp ((complex i).cylinderEndpoint a).nu F
    exact congrArg (fun g : OmegaCategory.Functor (complex i).nu Y => g.map x)
      (sourceCollapse_comp_truncated hk E)
  · intro r hr x hx
    change F.map ((sourceCollapse i k).cylinder.nu.map (verticalTable x)) = F.map (verticalTable x)
    rw [verticalTable_natural, sourceCollapse_bounded hr x hx]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma internalHom_truncated (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    {Y : OmegaCategory.{u}} {k : ℕ} (hk : Y.IsTruncated k) :
    (R.obj Y).IsTruncated k := by
  intro x
  obtain ⟨i,hi⟩ := (R.obj Y).finite_dimension x
  let F : (complex i).nu ⟶ R.obj Y := lift x hi
  let P : T.tensor.obj (complex i).nu ⟶ Y := (adj.homEquiv _ _).symm F
  let G : (complex i).cylinder.nu ⟶ Y := (T.globe i).inv ≫ P
  let q := sourceCollapse.{u} i k
  have hG : q.cylinder.nu ≫ G = G :=
    GrayRecursive.sourceCollapse_cylinder_truncated hk G
  have he : P = (T.globe i).hom ≫ G := by
    dsimp [G]
    simp
  have hP : T.tensor.map q.nu ≫ P = P := by
    calc
      T.tensor.map q.nu ≫ P = T.tensor.map q.nu ≫ (T.globe i).hom ≫ G := by rw [← he]
      _ = (T.globe i).hom ≫ q.cylinder.nu ≫ G := by
        rw [← Category.assoc, T.globe_natural, Category.assoc]
      _ = (T.globe i).hom ≫ G := by rw [hG]
      _ = P := he.symm
  have hF : q.nu ≫ F = F := by
    calc
      q.nu ≫ F = q.nu ≫ (adj.homEquiv _ _) P := by rw [Equiv.apply_symm_apply]
      _ = (adj.homEquiv _ _) (T.tensor.map q.nu ≫ P) :=
        (adj.homEquiv_naturality_left q.nu P).symm
      _ = (adj.homEquiv _ _) P := by rw [hP]
      _ = F := Equiv.apply_symm_apply _ _
  have hh := congrArg (fun f : (complex i).nu ⟶ R.obj Y => f.map (topTable i)) hF
  change F.map (q.nu.map (topTable i)) = F.map (topTable i) at hh
  rw [sourceCollapse_top] at hh
  change F.map ((complex i).nu.source k (topTable i)) = F.map (topTable i) at hh
  erw [F.map_source] at hh
  simpa only [F, lift_top] using hh

def truncatedCylinderEquiv (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k) :
    (T.tensor.obj (truncation k X).val ⟶ Y) ≃ (T.tensor.obj X ⟶ Y) :=
  ((adj.homEquiv (truncation k X).val Y).trans
    (truncationHomEquiv k X ⟨R.obj Y, T.internalHom_truncated R adj hk⟩)).trans
      (adj.homEquiv X Y).symm

lemma truncatedCylinderEquiv_apply (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (k : ℕ) (X Y : OmegaCategory.{u}) (hk : Y.IsTruncated k)
    (P : T.tensor.obj (truncation k X).val ⟶ Y) :
    T.truncatedCylinderEquiv R adj k X Y hk P = T.tensor.map (truncationUnit k X) ≫ P := by
  apply (adj.homEquiv X Y).injective
  change (adj.homEquiv X Y) ((adj.homEquiv X Y).symm
    (truncationUnit k X ≫ (adj.homEquiv (truncation k X).val Y) P)) = _
  erw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left]
  rfl

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

def finiteInternalHom (n : ℕ) : NCategory.{u} n ⥤ NCategory.{u} n where
  obj Y := ⟨R.obj Y.val, T.internalHom_truncated R adj Y.property⟩
  map f := R.map f
  map_id Y := R.map_id Y.val
  map_comp f g := R.map_comp f g

def finiteTranspose (n : ℕ) (X Y : NCategory.{u} n) :
    (T.tensor.obj X.val ⟶ Y.val) ≃ (X ⟶ (T.finiteInternalHom R adj n).obj Y) :=
  adj.homEquiv X.val Y.val

section FiniteDescent
variable {n : ℕ} {A B X Y Z : NCategory.{u} n}
variable {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
variable (sq : IsPushout i a b j)

def finiteGlue (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.obj Y.val ⟶ Z.val :=
  (T.finiteTranspose R adj n Y Z).symm
    (sq.desc ((T.finiteTranspose R adj n B Z) PB) ((T.finiteTranspose R adj n X Z) PX)
      (by
        change OmegaCategory.Functor.comp i ((adj.homEquiv _ _) PB) =
          OmegaCategory.Functor.comp a ((adj.homEquiv _ _) PX)
        exact (adj.homEquiv_naturality_left i PB).symm.trans
          ((congrArg (adj.homEquiv _ _) h).trans (adj.homEquiv_naturality_left a PX))))

lemma finiteGlue_left (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map b ≫ T.finiteGlue R adj sq PB PX h = PB := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change b ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inl_desc]
  rfl

lemma finiteGlue_right (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map j ≫ T.finiteGlue R adj sq PB PX h = PX := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left]
  change j ≫ (T.finiteTranspose R adj n Y Z)
    ((T.finiteTranspose R adj n Y Z).symm _) = _
  rw [Equiv.apply_symm_apply, sq.inr_desc]
  rfl

include R adj sq in
lemma finiteCylinder_hom_ext {P Q : T.tensor.obj Y.val ⟶ Z.val}
    (hb : T.tensor.map b ≫ P = T.tensor.map b ≫ Q)
    (hj : T.tensor.map j ≫ P = T.tensor.map j ≫ Q) : P = Q := by
  apply (T.finiteTranspose R adj n Y Z).injective
  apply sq.hom_ext
  · change OmegaCategory.Functor.comp b ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp b ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left b P).symm.trans
      ((congrArg (adj.homEquiv _ _) hb).trans (adj.homEquiv_naturality_left b Q))
  · change OmegaCategory.Functor.comp j ((adj.homEquiv _ _) P) =
      OmegaCategory.Functor.comp j ((adj.homEquiv _ _) Q)
    exact (adj.homEquiv_naturality_left j P).symm.trans
      ((congrArg (adj.homEquiv _ _) hj).trans (adj.homEquiv_naturality_left j Q))

lemma finiteGlue_endpoint_left
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp b
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app B.val ≫ PB := by
  have hb := (T.endpoint ε).naturality b
  exact (congrArg (fun f : B.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hb).trans
    (congrArg (fun f => (T.endpoint ε).app B.val ≫ f)
      (T.finiteGlue_left R adj sq PB PX h))

lemma finiteGlue_endpoint_right
    (PB : T.tensor.obj B.val ⟶ Z.val) (PX : T.tensor.obj X.val ⟶ Z.val)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    OmegaCategory.Functor.comp j
        ((T.endpoint ε).app Y.val ≫ T.finiteGlue R adj sq PB PX h) =
      (T.endpoint ε).app X.val ≫ PX := by
  have hj := (T.endpoint ε).naturality j
  exact (congrArg (fun f : X.val ⟶ T.tensor.obj Y.val =>
    f ≫ T.finiteGlue R adj sq PB PX h) hj).trans
    (congrArg (fun f => (T.endpoint ε).app X.val ≫ f)
      (T.finiteGlue_right R adj sq PB PX h))

include R adj sq in

theorem finite_stationary_gluing
    (P : T.tensor.obj B.val ⟶ B.val)
    (F : Bool → (B ⟶ B))
    (he : ∀ ε, (T.endpoint ε).app B.val ≫ P = F ε)
    (hs : T.tensor.map i ≫ P = (T.projection.app A.val) ≫ i) :
    ∃ Q : T.tensor.obj Y.val ⟶ Y.val,
      T.tensor.map b ≫ Q = P ≫ b ∧
      T.tensor.map j ≫ Q = T.projection.app X.val ≫ j ∧
      (∀ ε, OmegaCategory.Functor.comp b ((T.endpoint ε).app Y.val ≫ Q) = F ε ≫ b) ∧
      (∀ ε, OmegaCategory.Functor.comp j ((T.endpoint ε).app Y.val ≫ Q) = j) ∧
      (∀ Q' : T.tensor.obj Y.val ⟶ Y.val,
        T.tensor.map b ≫ Q' = P ≫ b →
        T.tensor.map j ≫ Q' = T.projection.app X.val ≫ j → Q' = Q) := by
  have hc : T.tensor.map i ≫ (P ≫ b) =
      T.tensor.map a ≫ (T.projection.app X.val ≫ j) := by
    calc
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from i ≫ b) := by
        rw [← Category.assoc, hs, Category.assoc]
      _ = (T.projection.app A.val) ≫ (show A.val ⟶ Y.val from a ≫ j) :=
        congrArg (fun f : A ⟶ Y => T.projection.app A.val ≫ f) sq.w
      _ = _ := by
        have ha := T.projection.naturality a
        change _ = (T.tensor.map a ≫ T.projection.app X.val) ≫ j
        rw [ha]
        rfl
  let Q := T.finiteGlue R adj sq (P ≫ b) (T.projection.app X.val ≫ j) hc
  refine ⟨Q, T.finiteGlue_left R adj sq _ _ hc,
    T.finiteGlue_right R adj sq _ _ hc, ?_, ?_, ?_⟩
  · intro ε
    rw [T.finiteGlue_endpoint_left, ← Category.assoc, he ε]
    rfl
  · intro ε
    rw [T.finiteGlue_endpoint_right, ← Category.assoc]
    have hε := congrArg (fun α => α.app X.val) (T.endpoint_projection ε)
    change (T.endpoint ε).app X.val ≫ T.projection.app X.val = 𝟙 X.val at hε
    rw [hε]; rfl
  · intro Q' hb hj
    apply T.finiteCylinder_hom_ext R adj sq
    · exact hb.trans (T.finiteGlue_left R adj sq _ _ hc).symm
    · exact hj.trans (T.finiteGlue_right R adj sq _ _ hc).symm

end FiniteDescent
end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Simplicial MonoidalCategory Opposite
open DirectedComplex NormalizedChains OmegaCategory

variable (T : RightIntervalExtension.{u})

lemma simplex_inverse_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] (f : Hom (complex P) (complex Q)) :
    f.cylinder.nu ≫ (T.simplex Q).inv = (T.simplex P).inv ≫ T.tensor.map f.nu := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← T.simplex_natural, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma cut_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] (f : P →o Q) (θ : Q →o Fin 2) :
    (complexMap f).nu ≫ T.cut θ = T.cut (θ.comp f) ≫ T.tensor.map (complexMap f).nu := by
  change (Hom.comp (complexMap f) (awHom θ)).nu ≫ (T.simplex Q).inv = _
  rw [awHom_naturality]
  change (awHom (θ.comp f)).nu ≫ ((complexMap f).cylinder.nu ≫ (T.simplex Q).inv) = _
  rw [T.simplex_inverse_natural]
  rfl

lemma cut_endpoint {P : Type u} [LinearOrder P] [Finite P] (ε : Bool) :
    T.cut (OrderHom.const P (if ε then 1 else 0)) = (T.endpoint ε).app (complex P).nu := by
  unfold cut
  rw [awHom_endpoint, ← T.simplex_endpoint, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def raiseSimplex {X : OmegaCategory.{u}} {m : ℕ} (F : OmegaCategory.Functor (Oriental m) X) :
    (complex (ULift.{u} (Fin (m+1)))).nu ⟶ X :=
  OmegaCategory.Functor.comp (complexMap (orderULiftDown _)).nu F

lemma up_raiseSimplex {X : OmegaCategory.{u}} {m : ℕ}
    (F : OmegaCategory.Functor (Oriental m) X) :
    OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
      (raiseSimplex F) = F := by
  have h := congrArg Hom.nu (complexMap_comp (orderULiftUp.{0,u} (Fin (m+1)))
    (orderULiftDown _))
  rw [orderULiftUp_down, complexMap_id] at h
  exact congrArg (fun a => OmegaCategory.Functor.comp a F) h.symm

lemma raiseSimplex_precomp {X : OmegaCategory.{u}} {m n : ℕ}
    (a : Fin (m+1) →o Fin (n+1)) (F : OmegaCategory.Functor (Oriental n) X) :
    raiseSimplex (OmegaCategory.Functor.comp (complexMap a).nu F) =
      (complexMap ((orderULiftUp _).comp (a.comp (orderULiftDown _)))).nu ≫
        raiseSimplex F := by
  have h₁ := complexMap_comp (orderULiftDown.{0,u} (Fin (m+1))) a
  have h₂ := complexMap_comp
    ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _))) (orderULiftDown _)
  have hc : (orderULiftDown (Fin (n+1))).comp
      ((orderULiftUp.{0,u} _).comp (a.comp (orderULiftDown _))) = a.comp (orderULiftDown _) := rfl
  rw [hc, h₁] at h₂
  exact congrArg (fun f => OmegaCategory.Functor.comp f.nu F) h₂

lemma up_simplexMap {m n : ℕ} (a : Fin (m+1) →o Fin (n+1)) :
    OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
      (complexMap ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _)))).nu =
    OmegaCategory.Functor.comp (complexMap a).nu
      (complexMap (orderULiftUp.{0,u} (Fin (n+1)))).nu := by
  have h₁ := complexMap_comp (orderULiftUp.{0,u} (Fin (m+1)))
    ((orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _)))
  have hc : ((orderULiftUp.{0,u} (Fin (n+1))).comp
    (a.comp (orderULiftDown _))).comp (orderULiftUp (Fin (m+1))) =
      (orderULiftUp _).comp a := rfl
  rw [hc, complexMap_comp] at h₁
  exact congrArg Hom.nu h₁.symm

def nerveCylinderSimplex {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X)
    (θ : Fin (m+1) →o Fin 2) : OmegaCategory.Functor (Oriental m) Y :=
  OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
    (T.cut (θ.comp (orderULiftDown _)) ≫ T.tensor.map (raiseSimplex F) ≫ P)

lemma nerveCylinderSimplex_natural {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) {m n : ℕ} (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) X) (θ : Fin (n+1) →o Fin 2) :
    T.nerveCylinderSimplex P m (OmegaCategory.Functor.comp (complexMap a).nu F)
      (θ.comp a) = OmegaCategory.Functor.comp (complexMap a).nu
        (T.nerveCylinderSimplex P n F θ) := by
  unfold nerveCylinderSimplex
  rw [raiseSimplex_precomp, T.tensor.map_comp]
  let b := (orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _))
  have hc : (θ.comp a).comp (orderULiftDown _) =
      (θ.comp (orderULiftDown _)).comp b := rfl
  rw [hc]
  have hcut := T.cut_natural b (θ.comp (orderULiftDown _))
  have h := congrArg (fun f => OmegaCategory.Functor.comp
    (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
    (f ≫ T.tensor.map (raiseSimplex F) ≫ P)) hcut.symm
  apply h.trans
  exact congrArg (fun f => OmegaCategory.Functor.comp f
    (T.cut (θ.comp (orderULiftDown _)) ≫ T.tensor.map (raiseSimplex F) ≫ P))
      (up_simplexMap a)

lemma nerveCylinderSimplex_endpoint {X Y : OmegaCategory.{u}}
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X) (ε : Bool) :
    T.nerveCylinderSimplex P m F (OrderHom.const _ (if ε then 1 else 0)) =
      OmegaCategory.Functor.comp F ((T.endpoint ε).app X ≫ P) := by
  unfold nerveCylinderSimplex
  have hc : (OrderHom.const (Fin (m+1)) (if ε then (1 : Fin 2) else 0)).comp
      (orderULiftDown.{0,u} (Fin (m+1))) = OrderHom.const _ (if ε then 1 else 0) := rfl
  rw [hc, T.cut_endpoint]
  have hn := (T.endpoint ε).naturality (raiseSimplex F)
  exact (congrArg (fun f => OmegaCategory.Functor.comp
    (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu (f ≫ P)) hn.symm).trans
    (congrArg (fun f => OmegaCategory.Functor.comp f ((T.endpoint ε).app X ≫ P))
      (up_raiseSimplex F))

def nerveCylinder {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y) :
    streetNerve X ⊗ Δ[1] ⟶ streetNerve Y where
  app m := ↾fun x => T.nerveCylinderSimplex P m.unop.len x.1
    (SSet.stdSimplex.objEquiv x.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro x
    exact T.nerveCylinderSimplex_natural P a.unop.toOrderHom x.1
      (SSet.stdSimplex.objEquiv x.2).toOrderHom

lemma nerveCylinder_endpoint {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y)
    (ε : Bool) : (if ε then SSet.ι₁ else SSet.ι₀) ≫ T.nerveCylinder P =
      streetNerveMap ((T.endpoint ε).app X ≫ P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  cases ε
  · exact T.nerveCylinderSimplex_endpoint P m.unop.len F false
  · exact T.nerveCylinderSimplex_endpoint P m.unop.len F true

def nerveHomotopy {X Y : OmegaCategory.{u}} (P : T.tensor.obj X ⟶ Y) :
    SSet.Homotopy (streetNerveMap ((T.endpoint false).app X ≫ P))
      (streetNerveMap ((T.endpoint true).app X ≫ P)) where
  h := T.nerveCylinder P
  h₀ := T.nerveCylinder_endpoint P false
  h₁ := T.nerveCylinder_endpoint P true
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, θ⟩
    exact False.elim hx

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData
open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

lemma finiteCylinderChainMap_stationary (σ : P →o E) (hs : ∀ p, σ p ∈ A) :
    d.finiteCylinderChainMap σ =
      Hom.comp (complex P).cylinderProjection (complexMap (d.finiteImageLeft σ)) := by
  ext p x
  apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype (d.finiteImage σ).vertices) p
  have h := congrArg (fun f => f.map p x) ((d.finiteCylinderChainMap_inclusion σ).trans
    (d.cylinderChainMap_stationary σ hs))
  have hc : Hom.comp (complexMap (d.finiteImageLeft σ))
      (complexMap (d.finiteImage σ).inclusion) = complexMap (d.f.comp σ) := by
    rw [← complexMap_comp]; rfl
  exact h.trans (congrArg (fun f => f.map p ((complex P).cylinderProjection.map p x)) hc.symm)

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

namespace FiniteVertexChain
variable {E P : Type u} [PartialOrder E] [PartialOrder P]

lemma map_lift (S : FiniteVertexChain E) (σ : P →o S.vertices) :
    posetCategorificationTableMap P ≫ (complexMap σ).nu ≫ S.lift =
      categorification.map (nerveMap (S.inclusion.comp σ).monotone.functor) := by
  rw [← Category.assoc, ← posetCategorificationTableMap_natural, lift, Category.assoc,
    IsIso.hom_inv_id_assoc, ← categorification.map_comp]
  rfl

end FiniteVertexChain
namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u})
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

lemma prismLeg_endpoint_false (σ : P →o E) :
    (T.endpoint false).app (categorification.obj (nerve P)) ≫ d.prismLeg T σ =
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [← Category.assoc, ← (T.endpoint false).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint false).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_false
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint false).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageLeft σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageLeft σ))

lemma prismLeg_endpoint_true (σ : P →o E) :
    (T.endpoint true).app (categorification.obj (nerve P)) ≫ d.prismLeg T σ =
      categorification.map (nerveMap (d.g.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [← Category.assoc, ← (T.endpoint true).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint true).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_true
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint true).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageRight σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageRight σ))

lemma prismLeg_stationary (σ : P →o E) (hs : ∀ p, σ p ∈ A) :
    d.prismLeg T σ = T.projection.app (categorification.obj (nerve P)) ≫
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [d.finiteCylinderChainMap_stationary σ hs]
  change T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫
    (complex P).cylinderProjection.nu ≫ (complexMap (d.finiteImageLeft σ)).nu ≫
      (d.finiteImage σ).lift = _
  rw [← Category.assoc (T.simplex P).hom, T.simplex_projection,
    ← Category.assoc (T.tensor.map (posetCategorificationTableMap P)),
    T.projection.naturality, Category.assoc, CategoryTheory.Functor.id_map, FiniteVertexChain.map_lift]
  rfl

lemma prism_leg (s : SimplexIndex E) :
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      d.prism T = d.prismLeg T (simplexVertexOrder s) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).fac (d.prismCocone T) s

lemma prism_endpoint_false :
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap d.f.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.f.monotone.functor)
  have hn := (T.endpoint false).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.prism_leg, d.prismLeg_endpoint_false]
  rw [← categorification.map_comp]
  congr 1

lemma prism_endpoint_true :
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap d.g.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.g.monotone.functor)
  have hn := (T.endpoint true).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.prism_leg, d.prismLeg_endpoint_true]
  rw [← categorification.map_comp]
  congr 1

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u})

lemma grayPrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.prism T =
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  apply (isColimitOfPreserves T.tensor (posetSimplexIsColimit P)).hom_ext
  intro s
  change T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.prism T =
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor)
  rw [← Category.assoc, ← T.tensor.map_comp, ← categorification.map_comp]
  have hvn : nerveMap (simplexVertexOrder s).monotone.functor ≫ nerveMap v.monotone.functor =
      nerveMap (simplexVertexOrder (s.postcompose v)).monotone.functor := by
    rw [simplexVertexOrder_postcompose]
    rfl
  erw [hvn, d.prism_leg, d.prismLeg_stationary T _ (fun p => hv _),
    ← Category.assoc, T.projection.naturality, CategoryTheory.Functor.id_map,
    Category.assoc, ← categorification.map_comp]
  congr 1

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u}) (R : OmegaCategory.{u} ⥤ OmegaCategory.{u})
variable (adj : T.tensor ⊣ R) (n : ℕ)

def finitePrism :
    T.tensor.obj ((categorificationFinite n).obj (nerve E)).val ⟶
      ((categorificationFinite n).obj (nerve E)).val :=
  (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve E))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).symm
      (d.prism T ≫ truncationUnit n (categorification.obj (nerve E)))

lemma finitePrism_unit :
    T.tensor.map (truncationUnit n (categorification.obj (nerve E))) ≫
      d.finitePrism T R adj n = d.prism T ≫ truncationUnit n (categorification.obj (nerve E)) := by
  erw [← T.truncatedCylinderEquiv_apply R adj n _ _
    ((categorificationFinite n).obj (nerve E)).property]
  exact Equiv.apply_symm_apply _ _

lemma finitePrism_endpoint_false :
    (T.endpoint false).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.finitePrism T R adj n = (categorificationFinite n).map (nerveMap d.f.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint false).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.finitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint false).app (categorification.obj (nerve E)) ≫ h)
        (d.finitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.prism_endpoint_false T)))

lemma finitePrism_endpoint_true :
    (T.endpoint true).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.finitePrism T R adj n = (categorificationFinite n).map (nerveMap d.g.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint true).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.finitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint true).app (categorification.obj (nerve E)) ≫ h)
        (d.finitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.prism_endpoint_true T)))

lemma finitePrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map ((categorificationFinite n).map (nerveMap v.monotone.functor)) ≫
      d.finitePrism T R adj n =
      T.projection.app ((categorificationFinite n).obj (nerve P)).val ≫
        (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor) := by
  apply (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve P))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).injective
  erw [T.truncatedCylinderEquiv_apply, T.truncatedCylinderEquiv_apply]
  erw [← Category.assoc, ← T.tensor.map_comp]
  have hn : truncationUnit n (categorification.obj (nerve P)) ≫
      (show ((categorificationFinite n).obj (nerve P)).val ⟶
          ((categorificationFinite n).obj (nerve E)).val from
      (categorificationFinite n).map (nerveMap v.monotone.functor)) =
      categorification.map (nerveMap v.monotone.functor) ≫
        truncationUnit n (categorification.obj (nerve E)) := rfl
  erw [hn, T.tensor.map_comp, Category.assoc, d.finitePrism_unit,
    ← Category.assoc, d.grayPrism_stationary T v hv,
    Category.assoc]
  exact congrArg (fun h : T.tensor.obj (categorification.obj (nerve P)) ⟶
      ((categorificationFinite n).obj (nerve P)).val =>
    h ≫ (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor))
      (T.projection.naturality (truncationUnit n (categorification.obj (nerve P)))).symm

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

include R adj in

theorem finite_pushout_zigzag
    {n : ℕ} {A B X Y : NCategory.{u} n}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i a b j)
    (r : B ⟶ A) (hi : i ≫ r = 𝟙 A) (G : B ⟶ B)
    (P₀ P₁ : T.tensor.obj B.val ⟶ B.val)
    (h₀ : (T.endpoint false).app B.val ≫ P₀ = 𝟙 B.val)
    (h₁ : (T.endpoint true).app B.val ≫ P₀ = G)
    (h₂ : (T.endpoint false).app B.val ≫ P₁ = r ≫ i)
    (h₃ : (T.endpoint true).app B.val ≫ P₁ = G)
    (hs₀ : T.tensor.map i ≫ P₀ = T.projection.app A.val ≫ i)
    (hs₁ : T.tensor.map i ≫ P₁ = T.projection.app A.val ≫ i) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let p : Y ⟶ X := sq.desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id])
  have hpB : b ≫ p = r ≫ a := sq.inl_desc _ _ _
  have hpX : j ≫ p = 𝟙 X := sq.inr_desc _ _ _
  obtain ⟨Q₀, _, _, hB₀, hX₀, _⟩ := T.finite_stationary_gluing R adj sq P₀
    (fun ε => if ε then G else 𝟙 B) (by intro ε; cases ε; exact h₀; exact h₁) hs₀
  obtain ⟨Q₁, _, _, hB₁, hX₁, _⟩ := T.finite_stationary_gluing R adj sq P₁
    (fun ε => if ε then G else r ≫ i) (by intro ε; cases ε; exact h₂; exact h₃) hs₁
  let e₀ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₀
  let e₁ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₁
  have he₀ : e₀ false = 𝟙 Y := by
    apply sq.hom_ext
    · exact hB₀ false
    · exact hX₀ false
  have he₁ : e₁ false = p ≫ j := by
    apply sq.hom_ext
    · rw [← Category.assoc, hpB, Category.assoc, ← sq.w, ← Category.assoc]
      exact hB₁ false
    · rw [← Category.assoc, hpX, Category.id_comp]
      exact hX₁ false
  have he : e₁ true = e₀ true := by
    apply sq.hom_ext
    · exact (hB₁ true).trans (hB₀ true).symm
    · exact (hX₁ true).trans (hX₀ true).symm
  refine ⟨p, e₀ true, hpX, ?_, ?_⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₀ false))
        ((streetNerveFinite n).map (e₀ true)) := T.nerveHomotopy Q₀
    rw [he₀, (streetNerveFinite n).map_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₁ false))
        ((streetNerveFinite n).map (e₁ true)) := T.nerveHomotopy Q₁
    rw [he₁, he] at h
    exact ⟨h⟩

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

include T R adj hA r hadj x hx in

theorem finite_pushout_deformation (n : ℕ)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let d₀ := idPrismData A hA x hx
  let d₁ := retractPrismData A hA r hadj x hx
  let i : A →o E := (OrderEmbedding.subtype A).toOrderHom
  let r' := retract A hA r hadj x hx
  have hr' : r'.comp i = OrderHom.id := retract_comp_inc A hA r hadj x hx
  have hri : inc n A ≫ posetMap n r' = 𝟙 (posetObj n A) := by
    rw [← finitePosetMap_comp]
    change posetMap n (r'.comp i) = _
    rw [hr', finitePosetMap_id]
  have h₀ : d₀.f.comp i = i := rfl
  have h₁ : d₁.f.comp i = i := by
    ext e
    exact congrArg Subtype.val (retract_old A hA r hadj x hx e)
  have hs₀ := d₀.finitePrism_stationary T R adj n i (fun e => e.property)
  have hs₁ := d₁.finitePrism_stationary T R adj n i (fun e => e.property)
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  exact T.finite_pushout_zigzag R adj sq (posetMap n r') hri
    (posetMap n (upper A hA x hx))
    (d₀.finitePrism T R adj n) (d₁.finitePrism T R adj n)
    ((d₀.finitePrism_endpoint_false T R adj n).trans (finitePosetMap_id n E))
    (d₀.finitePrism_endpoint_true T R adj n)
    ((d₁.finitePrism_endpoint_false T R adj n).trans (finitePosetMap_comp n r' i))
    (d₁.finitePrism_endpoint_true T R adj n) hs₀ hs₁

include T R adj hA r hadj x hx in

theorem finite_pushout_nerve_weak (n : ℕ)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  obtain ⟨p,H,hp,⟨H₀⟩,⟨H₁⟩⟩ := finite_pushout_deformation T R adj A hA r hadj x hx n sq
  exact RightIntervalExtension.finite_nerve_weak_of_zigzag j p H hp H₀ H₁

end Thomason.GreatestNew

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable {A B X Y Z : OmegaCategory.{u}}
variable {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
variable (sq : IsPushout i a b j)

include sq in

lemma omegaCylinder_pushout : IsPushout (T.tensor.map i) (T.tensor.map a)
    (T.tensor.map b) (T.tensor.map j) := by
  let := T.cocontinuous
  exact sq.map T.tensor

def omegaGlue (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) : T.tensor.obj Y ⟶ Z :=
  (T.omegaCylinder_pushout sq).desc PB PX h

lemma omegaGlue_left (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map b ≫ T.omegaGlue sq PB PX h = PB :=
  (T.omegaCylinder_pushout sq).inl_desc PB PX h

lemma omegaGlue_right (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map j ≫ T.omegaGlue sq PB PX h = PX :=
  (T.omegaCylinder_pushout sq).inr_desc PB PX h

include sq in
lemma omegaCylinder_hom_ext {P Q : T.tensor.obj Y ⟶ Z}
    (hb : T.tensor.map b ≫ P = T.tensor.map b ≫ Q)
    (hj : T.tensor.map j ≫ P = T.tensor.map j ≫ Q) : P = Q :=
  (T.omegaCylinder_pushout sq).hom_ext hb hj

lemma omegaGlue_endpoint_left
    (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    b ≫ (T.endpoint ε).app Y ≫ T.omegaGlue sq PB PX h =
      (T.endpoint ε).app B ≫ PB := by
  exact (congrArg (fun f : B ⟶ T.tensor.obj Y =>
    f ≫ T.omegaGlue sq PB PX h) ((T.endpoint ε).naturality b)).trans
    (congrArg (fun f => (T.endpoint ε).app B ≫ f) (T.omegaGlue_left sq PB PX h))

lemma omegaGlue_endpoint_right
    (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    j ≫ (T.endpoint ε).app Y ≫ T.omegaGlue sq PB PX h =
      (T.endpoint ε).app X ≫ PX := by
  exact (congrArg (fun f : X ⟶ T.tensor.obj Y =>
    f ≫ T.omegaGlue sq PB PX h) ((T.endpoint ε).naturality j)).trans
    (congrArg (fun f => (T.endpoint ε).app X ≫ f) (T.omegaGlue_right sq PB PX h))

include sq in

theorem omega_stationary_gluing
    (P : T.tensor.obj B ⟶ B) (F : Bool → (B ⟶ B))
    (he : ∀ ε, (T.endpoint ε).app B ≫ P = F ε)
    (hs : T.tensor.map i ≫ P = T.projection.app A ≫ i) :
    ∃ Q : T.tensor.obj Y ⟶ Y,
      T.tensor.map b ≫ Q = P ≫ b ∧
      T.tensor.map j ≫ Q = T.projection.app X ≫ j ∧
      (∀ ε, b ≫ (T.endpoint ε).app Y ≫ Q = F ε ≫ b) ∧
      (∀ ε, j ≫ (T.endpoint ε).app Y ≫ Q = j) ∧
      (∀ Q' : T.tensor.obj Y ⟶ Y,
        T.tensor.map b ≫ Q' = P ≫ b →
        T.tensor.map j ≫ Q' = T.projection.app X ≫ j → Q' = Q) := by
  have hc : T.tensor.map i ≫ (P ≫ b) =
      T.tensor.map a ≫ (T.projection.app X ≫ j) := by
    calc
      _ = T.projection.app A ≫ (i ≫ b) := by rw [← Category.assoc, hs, Category.assoc]
      _ = T.projection.app A ≫ (a ≫ j) := congrArg (fun f => T.projection.app A ≫ f) sq.w
      _ = _ := (congrArg (fun f : T.tensor.obj A ⟶ X => f ≫ j)
        (T.projection.naturality a)).symm
  let Q := T.omegaGlue sq (P ≫ b) (T.projection.app X ≫ j) hc
  refine ⟨Q, T.omegaGlue_left sq _ _ hc, T.omegaGlue_right sq _ _ hc, ?_, ?_, ?_⟩
  · intro ε
    rw [T.omegaGlue_endpoint_left, ← Category.assoc, he ε]
  · intro ε
    rw [T.omegaGlue_endpoint_right, ← Category.assoc]
    have hε := congrArg (fun α => α.app X) (T.endpoint_projection ε)
    change (T.endpoint ε).app X ≫ T.projection.app X = 𝟙 X at hε
    rw [hε]; rfl
  · intro Q' hb hj
    apply T.omegaCylinder_hom_ext sq
    · exact hb.trans (T.omegaGlue_left sq _ _ hc).symm
    · exact hj.trans (T.omegaGlue_right sq _ _ hc).symm

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})

include T in

theorem omega_pushout_zigzag
    {A B X Y : OmegaCategory.{u}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i a b j)
    (r : B ⟶ A) (hi : i ≫ r = 𝟙 A) (G : B ⟶ B)
    (P₀ P₁ : T.tensor.obj B ⟶ B)
    (h₀ : (T.endpoint false).app B ≫ P₀ = 𝟙 B)
    (h₁ : (T.endpoint true).app B ≫ P₀ = G)
    (h₂ : (T.endpoint false).app B ≫ P₁ = r ≫ i)
    (h₃ : (T.endpoint true).app B ≫ P₁ = G)
    (hs₀ : T.tensor.map i ≫ P₀ = T.projection.app A ≫ i)
    (hs₁ : T.tensor.map i ≫ P₁ = T.projection.app A ≫ i) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y))
        (streetNerveFunctor.map H)) ∧
      Nonempty (SSet.Homotopy (streetNerveFunctor.map (p ≫ j))
        (streetNerveFunctor.map H)) := by
  let p : Y ⟶ X := sq.desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id])
  have hpB : b ≫ p = r ≫ a := sq.inl_desc _ _ _
  have hpX : j ≫ p = 𝟙 X := sq.inr_desc _ _ _
  obtain ⟨Q₀, _, _, hB₀, hX₀, _⟩ := T.omega_stationary_gluing sq P₀
    (fun ε => if ε then G else 𝟙 B) (by intro ε; cases ε; exact h₀; exact h₁) hs₀
  obtain ⟨Q₁, _, _, hB₁, hX₁, _⟩ := T.omega_stationary_gluing sq P₁
    (fun ε => if ε then G else r ≫ i) (by intro ε; cases ε; exact h₂; exact h₃) hs₁
  let e₀ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y) Q₀
  let e₁ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y) Q₁
  have he₀ : e₀ false = 𝟙 Y := by
    apply sq.hom_ext
    · exact hB₀ false
    · exact hX₀ false
  have he₁ : e₁ false = p ≫ j := by
    apply sq.hom_ext
    · rw [← Category.assoc, hpB, Category.assoc, ← sq.w, ← Category.assoc]
      exact hB₁ false
    · rw [← Category.assoc, hpX, Category.id_comp]
      exact hX₁ false
  have he : e₁ true = e₀ true := by
    apply sq.hom_ext
    · exact (hB₁ true).trans (hB₀ true).symm
    · exact (hX₁ true).trans (hX₀ true).symm
  refine ⟨p, e₀ true, hpX, ?_, ?_⟩
  · have h : SSet.Homotopy (streetNerveFunctor.map (e₀ false))
        (streetNerveFunctor.map (e₀ true)) := T.nerveHomotopy Q₀
    rw [he₀, streetNerveFunctor.map_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy (streetNerveFunctor.map (e₁ false))
        (streetNerveFunctor.map (e₁ true)) := T.nerveHomotopy Q₁
    rw [he₁, he] at h
    exact ⟨h⟩

lemma omega_nerve_weak_of_zigzag {X Y : OmegaCategory.{u}}
    (j : X ⟶ Y) (p : Y ⟶ X) (H : Y ⟶ Y) (hp : j ≫ p = 𝟙 X)
    (h₀ : SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y)) (streetNerveFunctor.map H))
    (h₁ : SSet.Homotopy (streetNerveFunctor.map (p ≫ j)) (streetNerveFunctor.map H)) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  have hH : simplicialWeakEquivalences (streetNerveFunctor.map H) :=
    (simplicialWeakEquivalences_homotopy h₀).mp (simplicialWeakEquivalences.id_mem _)
  have hw : simplicialWeakEquivalences (streetNerveFunctor.map (p ≫ j)) :=
    (simplicialWeakEquivalences_homotopy h₁).mpr hH
  have rt : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc,hp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by ext <;> simp [hp] }
  exact simplicialWeakEquivalences.of_retract (rt.map streetNerveFunctor) hw

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory

abbrev omegaPosetObj (P : Type u) [PartialOrder P] : OmegaCategory.{u} :=
  categorification.obj (nerve P)

abbrev omegaPosetMap {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) : omegaPosetObj P ⟶ omegaPosetObj Q :=
  categorification.map (nerveMap f.toFunctor)

abbrev omegaInc {P : Type u} [PartialOrder P] (A : Set P) :=
  omegaPosetMap (P := A) (Q := P) (OrderEmbedding.subtype A).toOrderHom

lemma omegaPosetMap_id (E : Type u) [PartialOrder E] :
    omegaPosetMap (OrderHom.id : E →o E) = 𝟙 (omegaPosetObj E) :=
  categorification.map_id (nerve E)

lemma omegaPosetMap_comp {P Q R : Type u} [PartialOrder P]
    [PartialOrder Q] [PartialOrder R] (f : P →o Q) (g : Q →o R) :
    omegaPosetMap (g.comp f) = omegaPosetMap f ≫ omegaPosetMap g :=
  categorification.map_comp (nerveMap f.toFunctor) (nerveMap g.toFunctor)

variable (T : RightIntervalExtension.{u})
variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

include T hA r hadj x hx in

theorem omega_pushout_deformation
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X} {j : X ⟶ Y}
    {b : omegaPosetObj E ⟶ Y} (sq : IsPushout (omegaInc A) a b j) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y))
        (streetNerveFunctor.map H)) ∧
      Nonempty (SSet.Homotopy (streetNerveFunctor.map (p ≫ j))
        (streetNerveFunctor.map H)) := by
  let d₀ := idPrismData A hA x hx
  let d₁ := retractPrismData A hA r hadj x hx
  let i : A →o E := (OrderEmbedding.subtype A).toOrderHom
  let r' := retract A hA r hadj x hx
  have hr' : r'.comp i = OrderHom.id := retract_comp_inc A hA r hadj x hx
  have hri : omegaInc A ≫ omegaPosetMap r' = 𝟙 (omegaPosetObj A) := by
    rw [← omegaPosetMap_comp]
    change omegaPosetMap (r'.comp i) = _
    rw [hr', omegaPosetMap_id]
  have h₀ : d₀.f.comp i = i := rfl
  have h₁ : d₁.f.comp i = i := by
    ext e
    exact congrArg Subtype.val (retract_old A hA r hadj x hx e)
  have hs₀ := d₀.grayPrism_stationary T i (fun e => e.property)
  have hs₁ := d₁.grayPrism_stationary T i (fun e => e.property)
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  exact T.omega_pushout_zigzag sq (omegaPosetMap r') hri
    (omegaPosetMap (upper A hA x hx))
    (d₀.prism T) (d₁.prism T)
    ((d₀.prism_endpoint_false T).trans (omegaPosetMap_id E))
    (d₀.prism_endpoint_true T)
    ((d₁.prism_endpoint_false T).trans (omegaPosetMap_comp r' i))
    (d₁.prism_endpoint_true T) hs₀ hs₁

include T hA r hadj x hx in

theorem omega_pushout_nerve_weak
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X} {j : X ⟶ Y}
    {b : omegaPosetObj E ⟶ Y} (sq : IsPushout (omegaInc A) a b j) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  obtain ⟨p,H,hp,⟨H₀⟩,⟨H₁⟩⟩ := omega_pushout_deformation T A hA r hadj x hx sq
  exact RightIntervalExtension.omega_nerve_weak_of_zigzag j p H hp H₀ H₁

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
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison

theorem finite_poset_couniversal
    (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {E : Type u} [PartialOrder E] [Finite E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : posetObj n E ⟶ Y} (sq : IsPushout a (inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  classical
  suffices H : ∀ m : ℕ, ∀ (E : Type u) [PartialOrder E] [Finite E], Nat.card E = m →
      ∀ (A : Set E), IsLowerSet A → ∀ (r : E →o A),
      (∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e) →
      ∀ {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X) (j : X ⟶ Y)
        (v : posetObj n E ⟶ Y), IsPushout a (inc n A) j v →
        simplicialWeakEquivalences ((streetNerveFinite n).map j) from
    H (Nat.card E) E rfl A hA r hadj a j v sq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ hm A hA r hadj X Y a j v sq
    by_cases he : Aᶜ.Nonempty
    · rcases greatest_or_two_maximal Aᶜ he with ⟨x,hx⟩ | ⟨x,y,hx,hy,hxy⟩
      · exact GreatestNew.finite_pushout_nerve_weak T R adj A hA r hadj x hx n sq.flip
      · let S₁ : Set E := {x}ᶜ
        let S₂ : Set E := {y}ᶜ
        have h₁ : IsLowerSet S₁ := delete_max_lower (maximal_new_isMax hA hx)
        have h₂ : IsLowerSet S₂ := delete_max_lower (maximal_new_isMax hA hy)
        have hA₁ : A ⊆ S₁ := by
          intro z hz heq
          change z = x at heq
          exact hx.1 (heq ▸ hz)
        have hA₂ : A ⊆ S₂ := by
          intro z hz heq
          change z = y at heq
          exact hy.1 (heq ▸ hz)
        have hc : S₁ ∪ S₂ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          change z ≠ x ∨ z ≠ y
          by_cases hz : z = x
          · exact Or.inr (fun heq => hxy (hz.symm.trans heq))
          · exact Or.inl hz
        obtain ⟨T₁,T₂,hT₁,hT₂,hTc,hp₁,hp₂,hp₃⟩ :=
          sieve_finite_attachment_covers n hn A S₁ S₂ h₁ h₂ hA₁ hA₂ hc a j v sq
        have hpiece (S : Set E) (hAS : A ⊆ S) (e : E) (he : e ∉ S)
            (Z : Set Y.val.Objects) (hp : IsPosetFiniteAttachmentPiece n A S hAS a j v Z) :
            ∃ (jS : X ⟶ fullFinite n Y Z), jS ≫ fullFiniteInclusion n Y Z = j ∧
              simplicialWeakEquivalences ((streetNerveFinite n).map jS) := by
          obtain ⟨jS,vS,hjS,hvS,sqS⟩ := hp
          refine ⟨jS,hjS,?_⟩
          let eS := nestedOldIso (categorificationFinite n) A S hAS
          have sqS' : IsPushout (eS.hom ≫ a) (inc n {s : S | s.val ∈ A}) jS vS := by
            apply sqS.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
            · simp
            · simp only [Iso.refl_hom, Category.comp_id]
              exact nestedOldIso_inc (categorificationFinite n) A S hAS
            · simp
            · simp
          exact ih (Nat.card S) (hm ▸ Finite.card_subtype_lt he) S rfl
            {s : S | s.val ∈ A} (restricted_lower hA S)
            (restrictedRetract A S hAS r) (restricted_adjoint A S hAS r hadj)
            (eS.hom ≫ a) jS vS sqS'
        obtain ⟨j₁,hj₁,hw₁⟩ := hpiece S₁ hA₁ x (by simp [S₁]) T₁ hp₁
        obtain ⟨j₂,hj₂,hw₂⟩ := hpiece S₂ hA₂ y (by simp [S₂]) T₂ hp₂
        obtain ⟨j₃,hj₃,hw₃⟩ := hpiece (S₁ ∩ S₂) (fun _ ha => ⟨hA₁ ha,hA₂ ha⟩)
          x (by simp [S₁]) (T₁ ∩ T₂) hp₃
        apply weak_of_full_sieve_cover hT₁ hT₂ hTc ((streetNerveFinite n).map j)
          ((streetNerveFinite n).map j₁) ((streetNerveFinite n).map j₂)
          ((streetNerveFinite n).map j₃) _ _ _ hw₁ hw₂ hw₃
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₁)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₂)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₃)
    · have ha : ∀ e, e ∈ A := by
        intro e
        by_contra h
        exact he ⟨e,h⟩
      have : IsIso (inc n A) := isIso_subtype_all (categorificationFinite n) A ha
      have : IsIso j := sq.isIso_inl_of_isIso
      exact simplicialWeakEquivalences.of_isIso _

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison GreatestNew

theorem omega_finite_poset_couniversal
    (T : RightIntervalExtension.{u})
    {E : Type u} [PartialOrder E] [Finite E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X}
    {j : X ⟶ Y} {v : omegaPosetObj E ⟶ Y} (sq : IsPushout a (omegaInc A) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  classical
  suffices H : ∀ m : ℕ, ∀ (E : Type u) [PartialOrder E] [Finite E], Nat.card E = m →
      ∀ (A : Set E), IsLowerSet A → ∀ (r : E →o A),
      (∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e) →
      ∀ {X Y : OmegaCategory.{u}} (a : omegaPosetObj A ⟶ X) (j : X ⟶ Y)
        (v : omegaPosetObj E ⟶ Y), IsPushout a (omegaInc A) j v →
        simplicialWeakEquivalences (streetNerveFunctor.map j) from
    H (Nat.card E) E rfl A hA r hadj a j v sq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ hm A hA r hadj X Y a j v sq
    by_cases he : Aᶜ.Nonempty
    · rcases greatest_or_two_maximal Aᶜ he with ⟨x,hx⟩ | ⟨x,y,hx,hy,hxy⟩
      · exact GreatestNew.omega_pushout_nerve_weak T A hA r hadj x hx sq.flip
      · let S₁ : Set E := {x}ᶜ
        let S₂ : Set E := {y}ᶜ
        have h₁ : IsLowerSet S₁ := delete_max_lower (maximal_new_isMax hA hx)
        have h₂ : IsLowerSet S₂ := delete_max_lower (maximal_new_isMax hA hy)
        have hA₁ : A ⊆ S₁ := by
          intro z hz heq
          change z = x at heq
          exact hx.1 (heq ▸ hz)
        have hA₂ : A ⊆ S₂ := by
          intro z hz heq
          change z = y at heq
          exact hy.1 (heq ▸ hz)
        have hc : S₁ ∪ S₂ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          change z ≠ x ∨ z ≠ y
          by_cases hz : z = x
          · exact Or.inr (fun heq => hxy (hz.symm.trans heq))
          · exact Or.inl hz
        obtain ⟨T₁,T₂,hT₁,hT₂,hTc,hp₁,hp₂,hp₃⟩ :=
          sieve_attachment_covers A S₁ S₂ h₁ h₂ hA₁ hA₂ hc a j v sq
        have hpiece (S : Set E) (hAS : A ⊆ S) (e : E) (he : e ∉ S)
            (Z : Set Y.Objects) (hp : IsPosetAttachmentPiece A S hAS a j v Z) :
            ∃ (jS : X ⟶ (Y.fullOn Z).category), jS ≫ (Y.fullOn Z).inclusion = j ∧
              simplicialWeakEquivalences (streetNerveFunctor.map jS) := by
          obtain ⟨jS,vS,hjS,hvS,sqS⟩ := hp
          refine ⟨jS,hjS,?_⟩
          let eS := nestedOldIso categorification A S hAS
          have sqS' : IsPushout (eS.hom ≫ a) (omegaInc {s : S | s.val ∈ A}) jS vS := by
            apply sqS.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
            · simp
            · simp only [Iso.refl_hom, Category.comp_id]
              exact nestedOldIso_inc categorification A S hAS
            · simp
            · simp
          exact ih (Nat.card S) (hm ▸ Finite.card_subtype_lt he) S rfl
            {s : S | s.val ∈ A} (restricted_lower hA S)
            (restrictedRetract A S hAS r) (restricted_adjoint A S hAS r hadj)
            (eS.hom ≫ a) jS vS sqS'
        obtain ⟨j₁,hj₁,hw₁⟩ := hpiece S₁ hA₁ x (by simp [S₁]) T₁ hp₁
        obtain ⟨j₂,hj₂,hw₂⟩ := hpiece S₂ hA₂ y (by simp [S₂]) T₂ hp₂
        obtain ⟨j₃,hj₃,hw₃⟩ := hpiece (S₁ ∩ S₂) (fun _ ha => ⟨hA₁ ha,hA₂ ha⟩)
          x (by simp [S₁]) (T₁ ∩ T₂) hp₃
        apply weak_of_full_sieve_cover hT₁ hT₂ hTc (streetNerveFunctor.map j)
          (streetNerveFunctor.map j₁) (streetNerveFunctor.map j₂)
          (streetNerveFunctor.map j₃) _ _ _ hw₁ hw₂ hw₃
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₁)
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₂)
        · exact (Functor.map_comp streetNerveFunctor _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => streetNerveFunctor.map f) hj₃)
    · have ha : ∀ e, e ∈ A := by
        intro e
        by_contra h
        exact he ⟨e,h⟩
      have : IsIso (omegaInc A) := isIso_subtype_all categorification A ha
      have : IsIso j := sq.isIso_inl_of_isIso
      exact simplicialWeakEquivalences.of_isIso _

end Thomason.Couniversality

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

theorem poset_couniversal
    (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {E : Type u} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.NCategory.{u} n} {a : AttachmentComparison.posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : AttachmentComparison.posetObj n E ⟶ Y}
    (sq : IsPushout a (AttachmentComparison.inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let := (categorificationFiniteAdjunction n).leftAdjoint_preservesColimits
  exact couniversal_of_finite (categorificationFinite n) (streetNerveFinite n)
    (fun P _ _ A hA r hr _ _ a j v sq =>
      finite_poset_couniversal T R adj n hn A hA r hr sq) A hA r hadj a j v sq

theorem omega_poset_couniversal
    (T : RightIntervalExtension.{u})
    {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.{u}} {a : categorification.obj (nerve A) ⟶ X}
    {j : X ⟶ Y} {v : categorification.obj (nerve E) ⟶ Y}
    (sq : IsPushout a (categorification.map
      (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  let := categorificationAdjunction.leftAdjoint_preservesColimits
  exact couniversal_of_finite categorification streetNerveFunctor
    (fun P _ _ A hA r hr _ _ a j v sq =>
      omega_finite_poset_couniversal T A hA r hr sq) A hA r hadj a j v sq

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma gray_piece_couniversal (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A S : Set B) (hA : IsLowerSet A) (hAS : A ⊆ S)
    (r : S →o A) (hadj : ∀ (a : A) (s : S), a.val ≤ s.val ↔ a ≤ r s)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n S ⟶ Y)
    (sq : IsPushout a (sb n A S hAS) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let e := nestedOldIso (categorificationFinite n) A S hAS
  let r' : S →o {s : S | s.val ∈ A} :=
    ⟨fun s => ⟨⟨(r s).val,hAS (r s).property⟩,(r s).property⟩,
      fun _ _ h => r.monotone h⟩
  have sq' : IsPushout (e.hom ≫ a) (inc n {s : S | s.val ∈ A}) j v := by
    apply sq.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom,Category.comp_id]
      exact nestedOldIso_inc (categorificationFinite n) A S hAS
    · simp
    · simp
  exact poset_couniversal T R adj n hn {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma gray_comparison_local (T : RightIntervalExtension.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n B ⟶ Y) (sc : IsPushout a (inc n A) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite n).obj X ⟶ P}
    {lB : (streetNerveFinite n).obj (posetObj n B) ⟶ P}
    (ss : IsPushout ((streetNerveFinite n).map a) ((streetNerveFinite n).map (inc n A)) lX lB)
    (F : P ⟶ (streetNerveFinite n).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite n).map j)
    (hFB : lB ≫ F = (streetNerveFinite n).map v) : simplicialWeakEquivalences F := by
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
    attachment_nerve_cover n hn A Z C hZ hC hAZ disjoint_compl_right hcov a j v sc
  let N := streetNerveFinite n
  let e := N.map (sb n A Z hAZ)
  let b := N.map a
  let PZ := pushout b e
  let xZ := pushout.inl b e
  let zZ := pushout.inr b e
  let sZ := IsPushout.of_hasPushout b e
  let FZ : PZ ⟶ N.obj YZ := sZ.desc (N.map jZ) (N.map vZ) (by
    rw [← N.map_comp, ← N.map_comp, scZ.w])
  have hFZX : xZ ≫ FZ = N.map jZ := sZ.inl_desc _ _ _
  have hFZZ : zZ ≫ FZ = N.map vZ := sZ.inr_desc _ _ _
  have hwj : simplicialWeakEquivalences (N.map jZ) :=
    gray_piece_couniversal T R adj n hn A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    gray_piece_couniversal T R adj n hn A Z hA hAZ r hadj
      (𝟙 _) (sb n A Z hAZ) (𝟙 _) IsPushout.of_id_fst
  have hcE : Mono e := by
    let e' := nestedOldIso (categorificationFinite n) A Z hAZ
    have he' : sb n A Z hAZ = e'.inv ≫ inc n {z : Z | z.val ∈ A} := by
      calc
        _ = e'.inv ≫ (e'.hom ≫ sb n A Z hAZ) := by simp
        _ = _ := congrArg (e'.inv ≫ ·) (nestedOldIso_inc (categorificationFinite n) A Z hAZ)
    have : Mono (N.map (inc n {z : Z | z.val ∈ A})) :=
      finite_nerve_attachment_mono n hn _ (restricted_lower hA Z)
        (𝟙 _) _ (𝟙 _) IsPushout.of_id_fst
    dsimp [e]
    rw [he',CategoryTheory.Functor.map_comp]
    infer_instance
  have hwx : simplicialWeakEquivalences xZ := by
    have he : SSet.anodyneExtensions e := KanQuillen.anodyne_class.symm ▸ ⟨hcE,hwe⟩
    exact KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sZ he)
  have hwFZ : simplicialWeakEquivalences FZ :=
    simplicialWeakEquivalences.of_precomp xZ FZ hwx (hFZX ▸ hwj)
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc n Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc n Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc n Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc n Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover n hn Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb n (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := finite_nerve_inter_upper_mono n hn Z C hZ
  have hk : k ≫ FZ = N.map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc n C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc n C) ≫ lB) ≫ F = N.map (inc n C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_weak F (KanLocal.local_pushout_map k c FZ
    (GeometricRecognition.weak_local FZ hwFZ) sp sq' F hFpZ hFC)

end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z


namespace Thomason.OmegaAttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality
open AttachmentComparison (upward)

abbrev sb {P : Type u} [PartialOrder P] (A B : Set P) (h : A ⊆ B) :=
  categorification.map (nerveMap (subposetMap A B h).toFunctor)
abbrev inc {P : Type u} [PartialOrder P] (A : Set P) :=
  categorification.map (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ A)).toOrderHom.toFunctor)

@[reassoc] lemma sb_inc {P : Type u} [PartialOrder P]
    (A B : Set P) (h : A ⊆ B) : sb A B h ≫ inc B = inc A := by
  rw [← categorification.map_comp]
  rfl

end Thomason.OmegaAttachmentComparison

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

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

inductive RectangleCell (n : ℕ) : Type u
  | endpoint : Bool → Table (complex.{u} (n+1)) → RectangleCell n
  | edge : Bool → RectangleCell n
  | diagonal : Table (K.{u} n) → RectangleCell n

def RectangleCell.eval {n : ℕ} : RectangleCell.{u} n → Table (K.{u} (n+1))
  | .endpoint a x => atEnd a x
  | .edge a => verticalTable (vertex n a)
  | .diagonal x => up x

def intervalLabel {n : ℕ} (t : Table (K.{u} n)) (b : Bool) : ℤ :=
  mass n 0 (sideRow t true 0 b)

@[simp] lemma intervalLabel_end {n : ℕ} (a b : Bool) (x : Table (complex.{u} n)) :
    intervalLabel (atEnd a x) b = if a then 1 else 0 := by
  cases a <;> simp [intervalLabel, sideRow, atEnd, Hom.table, cylinderEndpoint,
    cylinderEndpointMap, table_mass_zero]
  exact map_zero (mass.{u} n 0)

@[simp] lemma intervalLabel_vertical {n : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    intervalLabel (verticalTable x) b = if b then 1 else 0 := by
  cases b <;> simp [intervalLabel, sideRow, verticalTable, verticalRow, table_mass_zero]
  exact map_zero (mass.{u} n 0)

@[simp] lemma intervalLabel_up {n : ℕ} (x : Table (K.{u} n)) (b : Bool) :
    intervalLabel (up x) b = if b then 1 else 0 := by
  cases b <;> simp [intervalLabel, sideRow, diagonalRow]
  exact map_zero (mass (n+1) 0)

@[simp] lemma project_end {n : ℕ} (a : Bool) (x : Table (complex.{u} n)) :
    project (atEnd a x) = x := by
  ext p b
  cases p <;> cases a <;>
    simp [project, atEnd, Hom.table, cylinderProjection, cylinderProjectionMap,
      cylinderEndpoint, cylinderEndpointMap]

@[simp] lemma project_vertical_vertex (n : ℕ) (a : Bool) :
    project (verticalTable (vertex.{u} n a)) = vertex n a := by
  ext p b
  cases p with
  | zero => cases b <;> simp [project, Hom.table, cylinderProjection,
      cylinderProjectionMap, verticalTable, verticalRow]
  | succ p =>
    simp only [project_row, sideRow, Bool.false_eq_true, ite_false, ite_true,
      verticalTable, verticalRow, vertex_succ]
    split_ifs <;> cases b <;> simp

@[simp] lemma vertex_label (n : ℕ) (a b : Bool) :
    ((vertex.{u} n a).row 0 b).val ⟨true⟩ = if a then 1 else 0 := by
  cases a <;> simp

@[simp] lemma project_up_label {n : ℕ} (x : Table (K.{u} n)) (b : Bool) :
    ((project (up x)).row 0 b).val ⟨true⟩ = if b then 1 else 0 := by
  cases b <;> simp [project, Hom.table, cylinderProjection, cylinderProjectionMap,
    diagonalRow]

lemma vertex_injective (n : ℕ) : Function.Injective (vertex.{u} n) := by
  intro a b h
  have h' := congrArg (fun t : Table (complex (n+1)) => (t.row 0 false).val ⟨true⟩) h
  simp only [vertex_label] at h'
  cases a <;> cases b <;> simp_all

lemma RectangleCell.eval_injective (n : ℕ) : Function.Injective (RectangleCell.eval.{u} (n := n)) := by
  intro x y h
  have hs := congrArg (fun t => intervalLabel t false) h
  have ht := congrArg (fun t => intervalLabel t true) h
  cases x with
  | endpoint a x =>
    cases y with
    | endpoint b y =>
      have hab : a = b := by cases a <;> cases b <;> simp only [RectangleCell.eval, intervalLabel_end,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
      subst b
      congr 1
      simpa [RectangleCell.eval] using congrArg project h
    | edge b => cases a <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_vertical,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | diagonal y => cases a <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_up,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
  | edge a =>
    cases y with
    | endpoint b y => cases b <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_vertical,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | edge b =>
      have hv : vertex n a = vertex n b := by simpa [RectangleCell.eval] using congrArg project h
      exact congrArg RectangleCell.edge (vertex_injective n hv)
    | diagonal y =>
      have hs := congrArg (fun t => ((project t).row 0 false).val ⟨true⟩) h
      have ht := congrArg (fun t => ((project t).row 0 true).val ⟨true⟩) h
      cases a <;> simp only [RectangleCell.eval,
        project_vertical_vertex, project_up_label, vertex_label, Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
  | diagonal x =>
    cases y with
    | endpoint b y => cases b <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_up,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | edge b =>
      have hs := congrArg (fun t => ((project t).row 0 false).val ⟨true⟩) h
      have ht := congrArg (fun t => ((project t).row 0 true).val ⟨true⟩) h
      cases b <;> simp only [RectangleCell.eval,
        project_vertical_vertex, project_up_label, vertex_label, Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | diagonal y => exact congrArg RectangleCell.diagonal (up_injective n h)

lemma RectangleCell.eval_surjective (n : ℕ) : Function.Surjective (RectangleCell.eval.{u} (n := n)) := by
  intro t
  rcases table_cases t with ⟨a,he⟩ | ⟨a,he⟩ | hd
  · exact ⟨.endpoint a (project t), he.symm⟩
  · exact ⟨.edge a, he.symm⟩
  · exact ⟨.diagonal (down t hd), up_down t hd⟩

def rectangleEquiv (n : ℕ) : RectangleCell.{u} n ≃ Table (K.{u} (n+1)) :=
  Equiv.ofBijective RectangleCell.eval ⟨RectangleCell.eval_injective n, RectangleCell.eval_surjective n⟩

@[simp] lemma rectangleEquiv_apply (n : ℕ) (x : RectangleCell.{u} n) :
    rectangleEquiv n x = x.eval := rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

lemma globe_succ_cases (n : ℕ) (x : Table (complex.{u} (n+1))) :
    (∃ a, x = vertex n a) ∨ ∃ y : Table (complex.{u} n), x = suspendTable y := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  cases p with
  | zero => exact Or.inl ⟨a,he⟩
  | succ p => exact Or.inr ⟨truncate p a (topTable n), he.trans (suspendTable_eq_face (n := n) (k := p) a).symm⟩

@[simp] lemma atEnd_truncate {n : ℕ} (a b : Bool) (x : Table (complex.{u} n)) (k : ℕ) :
    truncate k b (atEnd a x) = atEnd a (truncate k b x) := by
  exact ((complex n).cylinderEndpoint a).table_truncate k b x |>.symm

@[simp] lemma vertex_truncate (n k : ℕ) (a b : Bool) :
    truncate k b (vertex.{u} n a) = vertex n a := by
  simp [vertex, truncate_truncate]

@[simp] lemma edge_truncate_zero (n : ℕ) (a b : Bool) :
    truncate 0 b (verticalTable (vertex.{u} n a)) = atEnd b (vertex n a) := by
  ext p e
  cases p with
  | zero => cases b <;> simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow]
  | succ p => simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap]; rfl

@[simp] lemma edge_truncate_succ (n k : ℕ) (a b : Bool) :
    truncate (k+1) b (verticalTable (vertex.{u} n a)) = verticalTable (vertex n a) := by
  have h : truncate 1 false (verticalTable (vertex.{u} n a)) = verticalTable (vertex n a) :=
    vertical_fixed (vertex n a) (vertex_truncate n 0 a false)
  have he := (K (n+1)).nu.face_of_fixed h (show 1 ≤ k+1 by omega) b
  cases b <;> exact he

@[simp] lemma up_truncate_zero {n : ℕ} (b : Bool) (x : Table (K.{u} n)) :
    truncate 0 b (up x) = atEnd b (vertex n b) := by
  ext p e
  cases p with
  | zero => cases b <;> simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      diagonalRow]
  | succ p => simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap]; rfl

@[simp] lemma up_truncate_succ {n : ℕ} (k : ℕ) (b : Bool) (x : Table (K.{u} n)) :
    truncate (k+1) b (up x) = up (truncate k b x) := (up_truncate x k b).symm

@[simp] lemma suspend_truncate_zero {n : ℕ} (b : Bool) (x : Table (complex.{u} n)) :
    truncate 0 b (suspendTable x) = vertex n b := by
  ext p e
  cases p <;> simp

@[simp] lemma atEnd_vertex_eq (n : ℕ) (a b c d : Bool) :
    atEnd a (vertex.{u} n b) = atEnd c (vertex n d) ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hr : RectangleCell.endpoint a (vertex n b) = RectangleCell.endpoint c (vertex n d) :=
      RectangleCell.eval_injective n h
    obtain ⟨rfl,hbd⟩ := RectangleCell.endpoint.inj hr
    exact ⟨rfl, vertex_injective n hbd⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma nonobject_cases {n : ℕ} (x : Table (K.{u} (n+1)))
    (hx : truncate 0 false x ≠ x) :
    (∃ a, ∃ y : Table (complex.{u} n), x = atEnd a (suspendTable y)) ∨
      (∃ a, x = verticalTable (vertex n a)) ∨ ∃ y : Table (K.{u} n), x = up y := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x =>
    rcases globe_succ_cases n x with ⟨b,rfl⟩ | ⟨y,rfl⟩
    · exact False.elim (hx (by simp [RectangleCell.eval]))
    · exact Or.inl ⟨a,y,rfl⟩
  | edge a => exact Or.inr (Or.inl ⟨a,rfl⟩)
  | diagonal x => exact Or.inr (Or.inr ⟨x,rfl⟩)

def RectangleCell.truncate {n : ℕ} (k : ℕ) (b : Bool) : RectangleCell.{u} n → RectangleCell.{u} n
  | .endpoint a x => .endpoint a (DirectedComplex.Table.truncate (k+1) b x)
  | .edge a => .edge a
  | .diagonal x => .diagonal (DirectedComplex.Table.truncate k b x)

@[simp] lemma RectangleCell.eval_truncate {n : ℕ} (k : ℕ) (b : Bool) (x : RectangleCell.{u} n) :
    (x.truncate k b).eval = DirectedComplex.Table.truncate (k+1) b x.eval := by
  cases x <;> simp [RectangleCell.eval, RectangleCell.truncate]

lemma positive_matching_iff {n : ℕ} (k : ℕ) (x y : RectangleCell.{u} n) :
    DirectedComplex.Table.truncate (k+1) true x.eval =
        DirectedComplex.Table.truncate (k+1) false y.eval ↔
      x.truncate k true = y.truncate k false := by
  rw [← RectangleCell.eval_truncate, ← RectangleCell.eval_truncate]
  exact (RectangleCell.eval_injective n).eq_iff

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RectangleComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangle Composition. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

structure RectangleDiagram (n : ℕ) (Y : OmegaCategory.{v}) where
  ends : Bool → OmegaCategory.Functor (complex.{u} (n+1)).nu Y
  edge : Bool → Y.Cell
  edge_fixed : ∀ a, Y.source 1 (edge a) = edge a
  edge_source : ∀ a, Y.source 0 (edge a) = (ends false).map (vertex n a)
  edge_target : ∀ a, Y.target 0 (edge a) = (ends true).map (vertex n a)
  diagonal : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((ends false).map (vertex n false)) ((ends true).map (vertex n true)))
  left : ∀ x, (diagonal.map (atEnd false x)).val =
    Y.join 0 (edge false) ((ends true).map (suspendTable x))
  right : ∀ x, (diagonal.map (atEnd true x)).val =
    Y.join 0 ((ends false).map (suspendTable x)) (edge true)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y)

def interpret : RectangleCell.{u} n → Y.Cell
  | .endpoint a x => (D.ends a).map x
  | .edge a => D.edge a
  | .diagonal x => (D.diagonal.map x).val

def cellMap (x : Table (K.{u} (n+1))) : Y.Cell :=
  D.interpret ((rectangleEquiv n).symm x)

@[simp] lemma cellMap_eval (x : RectangleCell.{u} n) : D.cellMap x.eval = D.interpret x := by
  change D.interpret ((rectangleEquiv n).symm (rectangleEquiv n x)) = _
  rw [Equiv.symm_apply_apply]

@[simp] lemma cellMap_endpoint (a : Bool) (x : Table (complex.{u} (n+1))) :
    D.cellMap (atEnd a x) = (D.ends a).map x := D.cellMap_eval (.endpoint a x)
@[simp] lemma cellMap_edge (a : Bool) :
    D.cellMap (verticalTable (vertex n a)) = D.edge a := D.cellMap_eval (.edge a)
@[simp] lemma cellMap_up (x : Table (K.{u} n)) :
    D.cellMap (up x) = (D.diagonal.map x).val := D.cellMap_eval (.diagonal x)

lemma cellMap_truncate (k : ℕ) (b : Bool) (x : Table (K.{u} (n+1))) :
    D.cellMap (truncate k b x) = Y.face k b (D.cellMap x) := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x =>
    simp only [RectangleCell.eval, atEnd_truncate, cellMap_endpoint]
    cases b
    · exact (D.ends a).map_source k x
    · exact (D.ends a).map_target k x
  | edge a =>
    cases k with
    | zero =>
      simp only [RectangleCell.eval, edge_truncate_zero, cellMap_endpoint, cellMap_edge]
      cases b
      · exact (D.edge_source a).symm
      · exact (D.edge_target a).symm
    | succ k =>
      simp only [RectangleCell.eval, edge_truncate_succ, cellMap_edge]
      exact (Y.face_of_fixed (D.edge_fixed a) (show 1 ≤ k+1 by omega) b).symm
  | diagonal x =>
    cases k with
    | zero =>
      simp only [RectangleCell.eval, up_truncate_zero, cellMap_endpoint, cellMap_up]
      cases b
      · exact (D.diagonal.map x).property.1.symm
      · exact (D.diagonal.map x).property.2.symm
    | succ k =>
      simp only [RectangleCell.eval, up_truncate_succ, cellMap_up]
      cases b
      · exact congrArg Subtype.val (D.diagonal.map_source k x)
      · exact congrArg Subtype.val (D.diagonal.map_target k x)

lemma cellMap_composable (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) :
    Y.target k (D.cellMap x) = Y.source k (D.cellMap y) := by
  exact (D.cellMap_truncate k true x).symm.trans
    ((congrArg D.cellMap h).trans (D.cellMap_truncate k false y))

lemma cellMap_fixed (k : ℕ) (x : Table (K.{u} (n+1)))
    (h : truncate k false x = x) : Y.source k (D.cellMap x) = D.cellMap x := by
  exact (D.cellMap_truncate k false x).symm.trans (congrArg D.cellMap h)

lemma cellMap_comp_of_left_fixed (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) (hx : truncate k false x = x) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  change D.cellMap ((K (n+1)).nu.comp k x y h) = _
  rw [(K (n+1)).nu.comp_of_left_source_fixed k x y h hx,
    Y.join_left_unit k _ _ (D.cellMap_fixed k x hx) (D.cellMap_composable k x y h)]

lemma cellMap_comp_of_right_fixed (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) (hy : truncate k false y = y) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  change D.cellMap ((K (n+1)).nu.comp k x y h) = _
  rw [(K (n+1)).nu.comp_of_right_source_fixed k x y h hy,
    Y.join_right_unit k _ _ (D.cellMap_fixed k y hy) (D.cellMap_composable k x y h)]

lemma cellMap_comp_positive (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate (k+1) true x = truncate (k+1) false y) :
    D.cellMap (DirectedComplex.Table.comp (k+1) x y h) =
      Y.join (k+1) (D.cellMap x) (D.cellMap y) := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  obtain ⟨s,rfl⟩ := RectangleCell.eval_surjective n y
  have hm := (positive_matching_iff k r s).mp h
  cases r with
  | endpoint a x =>
    cases s with
    | endpoint b y =>
      obtain ⟨hab,hxy⟩ := RectangleCell.endpoint.inj hm
      subst b
      change truncate (k+1) true x = truncate (k+1) false y at hxy
      change D.cellMap (DirectedComplex.Table.comp (k+1) (atEnd a x) (atEnd a y) h) = _
      have hc : DirectedComplex.Table.comp (k+1) (atEnd a x) (atEnd a y) h =
          atEnd a (DirectedComplex.Table.comp (k+1) x y hxy) :=
        (((complex (n+1)).cylinderEndpoint a).table_comp (k+1) x y hxy h).symm
      rw [hc, cellMap_endpoint]
      simp only [RectangleCell.eval, cellMap_endpoint]
      change (D.ends a).map ((complex (n+1)).nu.comp (k+1) x y hxy) = _
      rw [(D.ends a).map_comp (k+1) x y hxy ((D.ends a).map_composable hxy),
        Y.join_eq (k+1) _ _ ((D.ends a).map_composable hxy)]
    | edge b => cases hm
    | diagonal y => cases hm
  | edge a =>
    cases s with
    | endpoint b y => cases hm
    | edge b =>
      have hab : a = b := RectangleCell.edge.inj hm
      subst b
      exact D.cellMap_comp_of_left_fixed (k+1) _ _ h (edge_truncate_succ n k a false)
    | diagonal y => cases hm
  | diagonal x =>
    cases s with
    | endpoint b y => cases hm
    | edge b => cases hm
    | diagonal y =>
      have hxy : truncate k true x = truncate k false y := RectangleCell.diagonal.inj hm
      change D.cellMap (DirectedComplex.Table.comp (k+1) (up x) (up y) h) = _
      rw [← up_comp x y hxy h, cellMap_up]
      simp only [RectangleCell.eval, cellMap_up]
      have hd := D.diagonal.map_comp k x y hxy (D.diagonal.map_composable hxy)
      have hd' := congrArg Subtype.val hd
      change _ = Y.comp (k+1) _ _ _ at hd'
      exact hd'.trans (Y.join_eq (k+1) _ _ _).symm

lemma cellMap_comp_zero (x y : Table (K.{u} (n+1)))
    (h : truncate 0 true x = truncate 0 false y) :
    D.cellMap (DirectedComplex.Table.comp 0 x y h) = Y.join 0 (D.cellMap x) (D.cellMap y) := by
  by_cases hx : truncate 0 false x = x
  · exact D.cellMap_comp_of_left_fixed 0 x y h hx
  by_cases hy : truncate 0 false y = y
  · exact D.cellMap_comp_of_right_fixed 0 x y h hy
  rcases nonobject_cases x hx with ⟨a,x,rfl⟩ | ⟨a,rfl⟩ | ⟨x,rfl⟩ <;>
    rcases nonobject_cases y hy with ⟨b,y,rfl⟩ | ⟨b,rfl⟩ | ⟨y,rfl⟩
  · simp only [atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [atEnd_truncate, suspend_truncate_zero, edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    obtain ⟨rfl,rfl⟩ := h
    rw [← up_endpoint_true, cellMap_up, D.right]
    simp
  · simp only [atEnd_truncate, suspend_truncate_zero, up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [edge_truncate_zero, atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    obtain ⟨rfl,rfl⟩ := h
    rw [← up_endpoint_false, cellMap_up, D.left]
    simp
  · simp only [edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [edge_truncate_zero, up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [up_truncate_zero, atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [up_truncate_zero, edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1

lemma cellMap_comp (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  cases k with
  | zero => exact D.cellMap_comp_zero x y h
  | succ k => exact D.cellMap_comp_positive k x y h

def lift : OmegaCategory.Functor (K.{u} (n+1)).nu Y where
  map := D.cellMap
  map_source k x := D.cellMap_truncate k false x
  map_target k x := D.cellMap_truncate k true x
  map_comp k x y h h' := (D.cellMap_comp k x y h).trans (Y.join_eq k _ _ h')

@[simp] lemma lift_endpoint (a : Bool) (x : Table (complex.{u} (n+1))) :
    D.lift.map (atEnd a x) = (D.ends a).map x := D.cellMap_endpoint a x
@[simp] lemma lift_edge (a : Bool) :
    D.lift.map (verticalTable (vertex n a)) = D.edge a := D.cellMap_edge a
@[simp] lemma lift_up (x : Table (K.{u} n)) :
    D.lift.map (up x) = (D.diagonal.map x).val := D.cellMap_up x

end RectangleDiagram
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

def extractDiagonal {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) :
    OmegaCategory.Functor (K.{u} n).nu
      (Y.homCategory (F.map (atEnd false (vertex n false)))
        (F.map (atEnd true (vertex n true)))) where
  map x := ⟨F.map (up x), by
    erw [← F.map_source, ← F.map_target]
    exact ⟨congrArg F.map (up_truncate_zero false x),
      congrArg F.map (up_truncate_zero true x)⟩⟩
  map_source k x := Subtype.ext (by
    change F.map (up (truncate k false x)) = Y.source (k+1) (F.map (up x))
    erw [up_truncate]; exact F.map_source _ _)
  map_target k x := Subtype.ext (by
    change F.map (up (truncate k true x)) = Y.target (k+1) (F.map (up x))
    erw [up_truncate]; exact F.map_target _ _)
  map_comp k x y h h' := Subtype.ext (by
    change F.map (up (DirectedComplex.Table.comp k x y h)) = Y.comp (k+1) _ _ _
    rw [up_comp x y h (up_composable h)]
    exact F.map_comp _ _ _ (up_composable h) (congrArg Subtype.val h'))

def rectangleDiagramOfFunctor {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) : RectangleDiagram.{u,v} n Y where
  ends a := OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu F
  edge a := F.map (verticalTable (vertex n a))
  edge_fixed a := by
    erw [← F.map_source]
    exact congrArg F.map (edge_truncate_succ n 0 a false)
  edge_source a := by
    erw [← F.map_source]
    exact congrArg F.map (edge_truncate_zero n a false)
  edge_target a := by
    erw [← F.map_target]
    exact congrArg F.map (edge_truncate_zero n a true)
  diagonal := extractDiagonal F
  left x := by
    change F.map (up (atEnd false x)) = _
    rw [up_endpoint_false]
    exact (F.map_comp 0 _ _ (up_endpoint_left_matching x) (F.map_composable (up_endpoint_left_matching x))).trans
      (Y.join_eq 0 _ _ _).symm
  right x := by
    change F.map (up (atEnd true x)) = _
    rw [up_endpoint_true]
    exact (F.map_comp 0 _ _ (up_endpoint_right_matching x) (F.map_composable (up_endpoint_right_matching x))).trans
      (Y.join_eq 0 _ _ _).symm

lemma functor_ext_rectangle {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (ends : ∀ a x, F.map (atEnd a x) = G.map (atEnd a x))
    (edge : ∀ a, F.map (verticalTable (vertex n a)) = G.map (verticalTable (vertex n a)))
    (diagonal : ∀ x, F.map (up x) = G.map (up x)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x => exact ends a x
  | edge a => exact edge a
  | diagonal x => exact diagonal x

@[simp] lemma rectangleDiagramOfFunctor_lift {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) : (rectangleDiagramOfFunctor F).lift = F := by
  apply functor_ext_rectangle
  · intro a x; exact RectangleDiagram.lift_endpoint _ a x
  · intro a; exact RectangleDiagram.lift_edge _ a
  · intro x; exact RectangleDiagram.lift_up _ x

end Thomason.GrayRecursive

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CylinderProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cylinder Profiles. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

structure PositiveAcyclic (M : DirectedComplex.{u}) : Prop where
  augmentation_nonneg : ∀ x ∈ M.positive 0, 0 ≤ M.augmentation x
  augmentation_zero : ∀ x ∈ M.positive 0, M.augmentation x = 0 → x = 0
  cycle_zero : ∀ p (x : M.Chain (p+1)), x ∈ M.positive (p+1) → M.d p x = 0 → x = 0

end Thomason.DirectedComplex

end

end OAI
end


