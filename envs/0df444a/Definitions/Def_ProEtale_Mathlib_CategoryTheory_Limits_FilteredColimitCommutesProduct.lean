-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:31.398379+00:00
-- url     : https://prove2.me/theorems/ba1abb6f-bf86-5aad-ad49-06f037aa7806
-- title:
--   Transferring the property that filtered colimits commute with products along a functor
-- statement:
--   A category $\mathcal C$ with products and filtered colimits satisfies *IPC* (of shape $\iota$) if for every family $(J_i)_{i\in\iota}$ of filtered categories and diagrams $F_i : J_i \to \mathcal C$, the canonical map
--   $$\operatorname*{colim}_{(j_i)\in\prod_i J_i} \prod_i F_i(j_i) \longrightarrow \prod_i \operatorname*{colim}_{J_i} F_i$$
--   is an isomorphism (the colimit cocone of the product diagram is the product of the colimit cocones). This file proves:
--
--   1. If $\mathcal C$ satisfies IPC of shape $\iota$ for every $\iota$ in universe $w$, then $\mathcal C$ satisfies IPC.
--   2. **Transfer.** Let $F : \mathcal C \to \mathcal D$ preserve filtered colimits and products of shape $\iota$, and reflect colimits of every shape $\prod_i J_i$ with $J_i$ filtered. If $\mathcal D$ satisfies IPC of shape $\iota$ then so does $\mathcal C$. Consequently, if $F$ preserves filtered colimits and limits and reflects filtered colimits, and $\mathcal D$ satisfies IPC, then so does $\mathcal C$.
--   3. Auxiliary natural isomorphisms: $\prod_i (G_i \circ F_i) \cong \prod_i G_i \circ \prod_i F_i$ for families of functors, and $F \circ \prod \cong \prod \circ (F)_i$ when $F$ preserves products; plus a simp lemma for the reflexive case of `Pi.eqToEquivalence`.
--
--   The transfer result is applied with the forgetful functor from commutative algebras to sets to deduce IPC for categories of algebras.
--
--   **Formalization Note** Main declarations: `CategoryTheory.Limits.IsIPC.of_isIPCOfShape`, `CategoryTheory.Limits.IsIPCOfShape.of_preservesFilteredColimitsOfSize`, `CategoryTheory.Limits.IsIPC.of_preservesFilteredColimitsOfSize`, `CategoryTheory.Functor.piCompIso`, `CategoryTheory.Limits.Pi.functorCompIso`, `CategoryTheory.Pi.eqToEquivalence_rfl`. IPC is Mathlib's `IsIPC.{w}`/`IsIPCOfShape.{w}`, with index categories in `Type w`. In item 2 the reflection hypothesis is stated for all families $J : \iota \to$ `Type w` of small filtered categories.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/FilteredColimitCommutesProduct.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe w

namespace CategoryTheory

variable {I J : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]


@[simp]
lemma Pi.eqToEquivalence_rfl {I : Type*} (C : I → Type*) [∀ i, Category* (C i)] (i : I) :
    Pi.eqToEquivalence C (refl i) = .refl :=
  rfl

attribute [-simp] Pi.equivalenceOfEquiv_functor Pi.equivalenceOfEquiv_inverse


@[simps!]
def Functor.piCompIso {I : Type*} {C D E : I → Type*} [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] [∀ i, Category* (E i)] (F : ∀ i, C i ⥤ D i) (G : ∀ i, D i ⥤ E i) :
    Functor.pi (fun i ↦ F i ⋙ G i) ≅ Functor.pi F ⋙ Functor.pi G :=
  NatIso.ofComponents (fun a ↦ Pi.isoMk fun i ↦ Iso.refl _)

namespace Limits

variable (ι : Type*) {C : Type*} [Category* C]

@[simps!]
noncomputable
def Pi.functorCompIso {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimitsOfShape (Discrete ι) F]
    [HasProductsOfShape ι C] [HasProductsOfShape ι D] :
    Pi.functor ι ⋙ F ≅ Functor.pi (fun _ ↦ F) ⋙ Pi.functor ι :=
  NatIso.ofComponents (fun a ↦ PreservesProduct.iso F a) fun {a b} f ↦ by
    apply Pi.hom_ext
    intro i
    suffices h : F.map (map f) ≫ F.map (π b i) = F.map (π a i) ≫ F.map (f i) by simpa [Functor.pi]
    rw [← F.map_comp, Pi.map_π]
    simp

variable {ι}
variable [HasProductsOfShape ι C] {J : ι → Type*} [∀ i, Category* (J i)]

lemma IsIPC.of_isIPCOfShape [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C]
    (h : ∀ (ι : Type w), IsIPCOfShape.{w} ι C) :
    IsIPC.{w} C where
  isIPCOfShape ι := h ι

lemma IsIPCOfShape.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    {ι : Type*} [HasProductsOfShape ι D] [IsIPCOfShape.{w} ι D] [HasProductsOfShape ι C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfShape (Discrete ι) F]
    -- TODO: this assumption is seemingly hard for typeclass search
    [∀ (J : ι → Type w) [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)],
      ReflectsColimitsOfShape (∀ i, J i) F] :
    IsIPCOfShape.{w} ι C where
  nonempty_isColimit J _ _ D c hc := by
    obtain ⟨h⟩ := IsIPCOfShape.nonempty_isColimit (fun i ↦ isColimitOfPreserves F (hc i))
    constructor
    apply isColimitOfReflects F
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ h
    · exact Functor.isoWhiskerRight (Functor.piCompIso _ _) _ ≪≫
        (Functor.associator _ _ _) ≪≫
        (Functor.isoWhiskerLeft _ <| (Pi.functorCompIso _ _).symm) ≪≫
        (Functor.associator _ _ _).symm
    · refine Cocone.ext (PreservesProduct.iso F _).symm ?_
      intro a
      dsimp
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      rw [← cancel_mono (PreservesProduct.iso F _).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro i
      simp [Functor.pi, NatTrans.pi, ← Functor.map_comp]

lemma IsIPC.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    [HasProducts D] [HasFilteredColimitsOfSize.{w, w} D] [IsIPC.{w} D]
    [HasProducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfSize.{w, w} F]
    [ReflectsFilteredColimitsOfSize.{w, w} F] :
    IsIPC.{w} C :=
  .of_isIPCOfShape fun ι ↦ by
    convert IsIPCOfShape.of_preservesFilteredColimitsOfSize.{w} F
    · infer_instance
    · infer_instance
    · intro J
      infer_instance

end Limits

end CategoryTheory


