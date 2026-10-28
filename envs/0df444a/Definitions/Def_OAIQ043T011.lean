-- Prove2me | Definitions.Def_OAIQ043T011
-- name    : OAIQ043T011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T10:07:26.341741+00:00
-- url     : https://prove2.me/theorems/ae8aa945-66c2-4dae-984d-a2d257a7afe7
-- title:
--   Definitions bundle OAIQ043T011 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.Thomason.omegaEndpointOfGray`.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: [`Thomason_AttachmentComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/AttachmentComparison.lean), [`Thomason_PartialPrisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/PartialPrisms.lean), [`Thomason_ProperTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/CategoryTheory/Thomason/Thomason/ProperTransfer.lean).
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`; the bundles `OAIQ043T008` and `OAIQ043T009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ043T012`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures
import Definitions.Def_OAIQ043T008
import Definitions.Def_OAIQ043T009

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


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma cutHom_const_one (f : PartialHom (complex E) (complex D) n) (hn : 0<n) :
    cutHom f hn (OrderHom.const E (1 : Fin 2)) =
      PartialHom.ofHom (complexMap (homVertexOrderHom f hn)) n := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro c
  exact Subtype.ext (cutTotal_const_one f hn c.val)

lemma homVertex_ofHom (a : E →o D) (b : E) :
    homVertex (PartialHom.ofHom (complexMap a) n) b = a b := by
  apply bracket_singleton_injective
  change bracket [homVertex (PartialHom.ofHom (complexMap a) n) b] = bracket [a b]
  rw [← homTotal_vertex,homTotal_map (PartialHom.ofHom (complexMap a) n) 0
    ⟨bracket [b],bracket_mem_grade [b]⟩]
  change map a (bracket [b]) = bracket [a b]
  rw [map_bracket a (by simp)]
  rfl

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains OmegaCategory

lemma finitePosetTableNerveMap_vertex (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    finitePosetTableNerveMap n P ≫ finiteTableNerveVertexMap n hn P = 𝟙 (nerve P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change PartialNormalized.homVertex (liftedPartial (OmegaCategory.Functor.comp
    (complexMap (posetSimplexOrder s)).nu (truncationUnit n (complex P).nu))) i = s.obj i
  rw [PartialNormalized.homVertex_congr_low _ (PartialHom.ofHom (complexMap (posetSimplexOrder s)) n)
    (liftedPartial_of_nu_below (complexMap (posetSimplexOrder s))) hn,
    PartialNormalized.homVertex_ofHom]
  rfl

end Thomason

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


namespace Thomason.OmegaAttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality
open AttachmentComparison (upward)

lemma attachment_nerve_cover {P : Type u} [PartialOrder P]
    (A Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAZ : A ⊆ Z) (hAC : Disjoint A C) (hcover : Z ∪ C = Set.univ)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X) (j : X ⟶ Y)
    (v : posetObj P ⟶ Y) (sc : IsPushout a (inc A) j v) :
    ∃ (YZ : OmegaCategory.{u}) (jZ : X ⟶ YZ) (vZ : posetObj Z ⟶ YZ) (uZ : YZ ⟶ Y),
      IsPushout a (sb A Z hAZ) jZ vZ ∧ jZ ≫ uZ = j ∧ vZ ≫ uZ = inc Z ≫ v ∧
      IsPushout (streetNerveFunctor.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ))
        (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right))
        (streetNerveFunctor.map uZ) (streetNerveFunctor.map (inc C ≫ v)) := by
  obtain ⟨T₁,T₂,hT₁,hT₂,hTc,⟨jZ,vZ,hj,hv,sz⟩,⟨e₂,he₂⟩,⟨e₃,he₃⟩⟩ :=
    cosieve_attachment_covers A Z C hZ hC hAZ hAC hcover a j v sc
  let N := streetNerveFunctor
  let u₁ := (Y.fullOn T₁).inclusion
  let u₂ := (Y.fullOn T₂).inclusion
  let u₃ := (Y.fullOn (T₁ ∩ T₂)).inclusion
  let p₁ : (Y.fullOn (T₁ ∩ T₂)).category ⟶ (Y.fullOn T₁).category :=
    fullOnMap Set.inter_subset_left
  let p₂ : (Y.fullOn (T₁ ∩ T₂)).category ⟶ (Y.fullOn T₂).category :=
    fullOnMap Set.inter_subset_right
  change vZ ≫ u₁ = inc Z ≫ v at hv
  change e₂.hom ≫ u₂ = inc C ≫ v at he₂
  change e₃.hom ≫ u₃ = inc (Z ∩ C) ≫ v at he₃
  have hu₁ : p₁ ≫ u₁ = u₃ := rfl
  have hu₂ : p₂ ≫ u₂ = u₃ := rfl
  have : Mono (N.map u₁) := fullInclusion_nerve_mono Y T₁
  have : Mono (N.map u₂) := fullInclusion_nerve_mono Y T₂
  have sq : IsPushout (N.map p₁) (N.map p₂) (N.map u₁) (N.map u₂) :=
    cosieve_cover_nerve_isPushout hT₁ hT₂ (fun x => by
      have hx : x ∈ T₁ ∪ T₂ := by rw [hTc]; trivial
      exact hx)
  refine ⟨(Y.fullOn T₁).category, jZ, vZ, u₁, sz, hj, hv, ?_⟩
  apply sq.of_iso' (N.mapIso e₃) (Iso.refl _) (N.mapIso e₂) (Iso.refl _)
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₃.hom ≫ N.map p₁ = N.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ)
    apply (cancel_mono (N.map u₁)).mp
    simp only [← N.map_comp, Category.assoc, hu₁, he₃, hv]
    rw [sb_inc_assoc]
  · simp only [CategoryTheory.Functor.mapIso_hom]
    change N.map e₃.hom ≫ N.map p₂ = N.map (sb (Z ∩ C) C Set.inter_subset_right) ≫ N.map e₂.hom
    apply (cancel_mono (N.map u₂)).mp
    simp only [← N.map_comp, Category.assoc, hu₂, he₃, he₂]
    rw [sb_inc_assoc]
  · simp [N]
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₂.hom ≫ N.map u₂ = N.map (inc C ≫ v)
    rw [← N.map_comp, he₂]

lemma poset_nerve_cover {P : Type u} [PartialOrder P]
    (Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hcover : Z ∪ C = Set.univ) :
    IsPushout (streetNerveFunctor.map (sb (Z ∩ C) Z Set.inter_subset_left))
      (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right))
      (streetNerveFunctor.map (inc Z)) (streetNerveFunctor.map (inc C)) := by
  obtain ⟨YZ,jZ,vZ,uZ,sz,hj,hv,sq⟩ := attachment_nerve_cover (∅ : Set P) Z C
    hZ hC (Set.empty_subset Z) (by simp) hcover
    (𝟙 (posetObj (∅ : Set P))) (inc (∅ : Set P)) (𝟙 (posetObj P))
    (IsPushout.of_id_fst)
  have : IsIso vZ := sz.isIso_inr_of_isIso
  let N := streetNerveFunctor
  apply sq.of_iso' (Iso.refl _) (N.mapIso (asIso vZ)) (Iso.refl _) (Iso.refl _)
  · simp [N]
  · simp
  · simp only [CategoryTheory.Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map vZ ≫ N.map uZ = N.map (inc Z)
    rw [← N.map_comp, hv, Category.comp_id]
  · simp

lemma nerve_attachment_mono     {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj B ⟶ Y) (sc : IsPushout a (inc A) j v) :
    Mono (streetNerveFunctor.map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_sieve_attachment A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.fullOn S)
  have : Mono j := by
    rw [← he]
    infer_instance
  let : PreservesLimits streetNerveFunctor :=
    categorificationAdjunction.rightAdjoint_preservesLimits
  infer_instance

lemma nerve_upper_mono     {P : Type u} [PartialOrder P] (S : Set P) (hS : IsUpperSet S) :
    Mono (streetNerveFunctor.map (inc S)) := by
  let l := NormalizedChains.PosetTables.upperSegmentLabel S hS
  have hS' : S = {p | l p = 1} := by
    ext p
    exact (NormalizedChains.PosetTables.upperSegmentLabel_one S hS p).symm
  let e := posetPieceFiberIso S l 1 hS'
  have he := posetPieceFiberIso_inclusion S l 1 hS'
  have := OmegaCategory.Subcategory.inclusion_mono
    ((posetCategorificationLabel l).fiber (intervalVertex 1))
  have : Mono (inc S) := by
    change Mono (categorification.map
      (nerveMap (OrderEmbedding.subtype (fun element : P => element ∈ S)).toOrderHom.monotone.functor))
    rw [← he]
    infer_instance
  let : PreservesLimits streetNerveFunctor :=
    categorificationAdjunction.rightAdjoint_preservesLimits
  infer_instance

lemma nerve_inter_upper_mono     {P : Type u} [PartialOrder P] (Z C : Set P) (hZ : IsUpperSet Z) :
    Mono (streetNerveFunctor.map (sb (Z ∩ C) C Set.inter_subset_right)) := by
  let e := nestedOldIso categorification (Z ∩ C) C Set.inter_subset_right
  have : Mono (streetNerveFunctor.map (inc {c : C | c.val ∈ Z ∩ C})) :=
    nerve_upper_mono _ (by
      intro x y hxy hx
      exact ⟨hZ hxy hx.1,y.property⟩)
  have he : sb (Z ∩ C) C Set.inter_subset_right =
      e.inv ≫ inc {c : C | c.val ∈ Z ∩ C} := by
    calc
      _ = e.inv ≫ (e.hom ≫ sb (Z ∩ C) C Set.inter_subset_right) := by simp
      _ = _ := congrArg (e.inv ≫ ·) (nestedOldIso_inc
        categorification (Z ∩ C) C Set.inter_subset_right)
  rw [he, CategoryTheory.Functor.map_comp]
  infer_instance

lemma gray_piece_couniversal (T : RightIntervalExtension.{u})
    {B : Type u} [PartialOrder B]
    (A S : Set B) (hA : IsLowerSet A) (hAS : A ⊆ S)
    (r : S →o A) (hadj : ∀ (a : A) (s : S), a.val ≤ s.val ↔ a ≤ r s)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj S ⟶ Y)
    (sq : IsPushout a (sb A S hAS) j v) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  let e := nestedOldIso categorification A S hAS
  let r' : S →o {s : S | s.val ∈ A} :=
    ⟨fun s => ⟨⟨(r s).val,hAS (r s).property⟩,(r s).property⟩,
      fun _ _ h => r.monotone h⟩
  have sq' : IsPushout (e.hom ≫ a) (inc {s : S | s.val ∈ A}) j v := by
    apply sq.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom,Category.comp_id]
      exact nestedOldIso_inc categorification A S hAS
    · simp
    · simp
  exact omega_poset_couniversal T {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma gray_comparison_local (T : RightIntervalExtension.{u})
    {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : OmegaCategory.{u}} (a : posetObj A ⟶ X)
    (j : X ⟶ Y) (v : posetObj B ⟶ Y) (sc : IsPushout a (inc A) j v)
    {P : SSet.{u}} {lX : streetNerveFunctor.obj X ⟶ P}
    {lB : streetNerveFunctor.obj (posetObj B) ⟶ P}
    (ss : IsPushout (streetNerveFunctor.map a) (streetNerveFunctor.map (inc A)) lX lB)
    (F : P ⟶ streetNerveFunctor.obj Y)
    (hFX : lX ≫ F = streetNerveFunctor.map j)
    (hFB : lB ≫ F = streetNerveFunctor.map v) : simplicialWeakEquivalences F := by
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
    attachment_nerve_cover A Z C hZ hC hAZ disjoint_compl_right hcov a j v sc
  let N := streetNerveFunctor
  let e := N.map (sb A Z hAZ)
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
    gray_piece_couniversal T A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    gray_piece_couniversal T A Z hA hAZ r hadj
      (𝟙 _) (sb A Z hAZ) (𝟙 _) IsPushout.of_id_fst
  have hcE : Mono e := by
    let e' := nestedOldIso categorification A Z hAZ
    have he' : sb A Z hAZ = e'.inv ≫ inc {z : Z | z.val ∈ A} := by
      calc
        _ = e'.inv ≫ (e'.hom ≫ sb A Z hAZ) := by simp
        _ = _ := congrArg (e'.inv ≫ ·) (nestedOldIso_inc categorification A Z hAZ)
    have : Mono (N.map (inc {z : Z | z.val ∈ A})) :=
      nerve_attachment_mono _ (restricted_lower hA Z)
        (𝟙 _) _ (𝟙 _) IsPushout.of_id_fst
    dsimp [e]
    rw [he',CategoryTheory.Functor.map_comp]
    infer_instance
  have hwx : simplicialWeakEquivalences xZ := by
    have he : SSet.anodyneExtensions e := KanQuillen.anodyne_class.symm ▸ ⟨hcE,hwe⟩
    exact KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sZ he)
  have hwFZ : simplicialWeakEquivalences FZ :=
    simplicialWeakEquivalences.of_precomp xZ FZ hwx (hFZX ▸ hwj)
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := nerve_inter_upper_mono Z C hZ
  have hk : k ≫ FZ = N.map (sb (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc C) ≫ lB) ≫ F = N.map (inc C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_weak F (KanLocal.local_pushout_map k c FZ
    (GeometricRecognition.weak_local FZ hwFZ) sp sq' F hFpZ hFC)

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


namespace Thomason
open CategoryTheory Limits AbstractTransfer
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem omegaPosetComparison (T : RightIntervalExtension.{u}) :
    PosetComparison categorification.{u} streetNerveFunctor categorificationAdjunction := by
  exact {
    unit_weak := posetCategorificationUnit_weakEquivalence
    attachment_mono := OmegaAttachmentComparison.nerve_attachment_mono
    comparison := OmegaAttachmentComparison.gray_comparison_local T }

def omegaEndpointOfGray (T : RightIntervalExtension.{u}) :
    ExactModelEndpoint thomasonLeft.{u} thomasonRight thomasonAdjunction := by
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (hornImages (L categorification.{u})) Cardinal.aleph0.{u} := thomasonHorn_smallCardinal
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (boundaryImages (L categorification.{u})) Cardinal.aleph0.{u} := thomasonBoundary_smallCardinal
  exact AbstractTransfer.exactEndpoint (omegaPosetComparison T)

end Thomason

end

end OAI
end


