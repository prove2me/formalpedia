-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_StructuredArrow_Basic
-- name    : ProEtale_Mathlib_CategoryTheory_Comma_StructuredArrow_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:20.181708+00:00
-- url     : https://prove2.me/theorems/f379596c-1e09-4267-8c67-b41bf2419e91
-- title:
--   Lifting a functor with a cocone over L to costructured arrows
-- statement:
--   Let $F : \mathcal J \to \mathcal C$ and $L : \mathcal C \to \mathcal D$ be functors, $X \in \mathcal D$, and $s : L \circ F \Rightarrow \Delta X$ a natural transformation to the constant functor (a cocone on $L\circ F$ with apex $X$). The file defines the functor
--   $$\mathcal J \longrightarrow (L \downarrow X), \qquad j \mapsto \big(F(j),\ s_j : L(F(j)) \to X\big),$$
--   into the category of costructured arrows, and proves that composing it with the projection $(L\downarrow X) \to \mathcal C$ gives back $F$ (definitionally).
--
--   This is a convenience construction for building diagrams in comma categories, used when presenting objects as limits or colimits over costructured arrows.
--
--   **Formalization Note** Main declarations: `CategoryTheory.CostructuredArrow.lift` (with `simps` lemmas for objects and morphisms) and the simp lemma `CategoryTheory.CostructuredArrow.lift_forget`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

@[simps! obj_left obj_hom map_left]
def CostructuredArrow.lift {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C)
    {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    J ⥤ CostructuredArrow L X where
  obj j := .mk (s.app j)
  map {i j} f := CostructuredArrow.homMk (F.map f) (by simp [← Functor.comp_map])

@[simp]
lemma CostructuredArrow.lift_forget {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C) {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    lift F s ⋙ CategoryTheory.CostructuredArrow.proj _ _ = F :=
  rfl

end CategoryTheory


