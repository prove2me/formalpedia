-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_DenseSubsite_Basic
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_DenseSubsite_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:30.5458+00:00
-- url     : https://prove2.me/theorems/cffafaa5-84af-5c28-a204-28937ad9e26e
-- title:
--   Compatibility of sheafification with restriction along a dense subsite
-- statement:
--   Let $G : C \to D$ be a functor, $J$ and $K$ Grothendieck topologies on $C$ and $D$, and $\mathcal A$ a category of coefficients.
--
--   1. If $G$ is cover-dense and locally full, the inverse of the bijection "restricting morphisms from a presheaf $F$ on $D$ to a sheaf $F'$ on $D$" is whiskering with $G^{\mathrm{op}}$: it sends $f : F \to F'$ to $G^{\mathrm{op}} f : F \circ G^{\mathrm{op}} \to F' \circ G^{\mathrm{op}}$. This holds by definition.
--   2. Let $G$ be a dense subsite with restriction of sheaves $\mathrm{Sh}(D,K) \to \mathrm{Sh}(C,J)$ an equivalence, and let $J$-sheafification exist. For a presheaf $F$ on $D$, the canonical map $F \circ G^{\mathrm{op}} \to a_J(F \circ G^{\mathrm{op}})$ followed by the isomorphism `sheafifyOfIsEquivalenceCompIso` equals the restriction along $G$ of the unit of the sheafification adjunction built from the equivalence.
--   3. If moreover $K$-sheafification exists, the canonical map $F \circ G^{\mathrm{op}} \to a_J(F \circ G^{\mathrm{op}})$ followed by the compatibility isomorphism $a_J(F \circ G^{\mathrm{op}}) \cong (a_K F) \circ G^{\mathrm{op}}$ equals the restriction along $G$ of $F \to a_K F$:
--   $$\big(F \circ G^{\mathrm{op}} \to a_J(F \circ G^{\mathrm{op}}) \xrightarrow{\ \sim\ } (a_K F) \circ G^{\mathrm{op}}\big) \;=\; G^{\mathrm{op}}\big(F \to a_K F\big).$$
--
--   These simp lemmas are used to compare sheafification on the affine and full pro-étale (or étale) sites.
--
--   **Formalization Note** Declarations: `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_symm_apply`, `Functor.IsDenseSubsite.toSheafify_sheafifyOfIsEquivalenceCompIso_inv_app_hom` and `Functor.IsDenseSubsite.toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom`. Both are tagged `@[reassoc (attr := simp)]`. Item 2 involves the inverse of `sheafifyOfIsEquivalenceCompIso` and the unit of `sheafifyAdjunctionOfIsEquivalence`. Item 3 uses `sheafEquivSheafificationCompatibility`. Only `HasWeakSheafify` is assumed.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) (A : Type*) [Category* A]

lemma IsCoverDense.restrictHomEquivHom_symm_apply [G.IsCoverDense K]
    [G.IsLocallyFull K] {F : Dᵒᵖ ⥤ A} {F' : Sheaf K A}
    (f : F ⟶ F'.obj) :
    restrictHomEquivHom (G := G).symm f = G.op.whiskerLeft f :=
  rfl

namespace IsDenseSubsite

variable [IsDenseSubsite J K G]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence]
  [HasWeakSheafify J A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafifyOfIsEquivalenceCompIso_inv_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify J (G.op ⋙ F) ≫
      ((sheafifyOfIsEquivalenceCompIso J K G A).inv.app F).hom =
      G.op.whiskerLeft ((sheafifyAdjunctionOfIsEquivalence _ _ _ _).unit.app _) := by
  have := isLocallyFull J K G
  have := isCoverDense J K G
  simp only [sheafifyOfIsEquivalenceCompIso, isoWhiskerLeft_trans, isoWhiskerLeft_twice,
    Iso.trans_assoc, Iso.trans_inv, isoWhiskerLeft_inv, Category.assoc, Iso.symm_inv,
    NatTrans.comp_app, comp_obj, whiskeringLeft_obj_obj, id_obj, whiskerLeft_app,
    rightUnitor_inv_app, associator_inv_app, associator_hom_app, Category.comp_id, Category.id_comp,
    sheafifyAdjunctionOfIsEquivalence, sheafifyHomEquivOfIsEquivalence, Equivalence.symm_functor,
    Equivalence.symm_inverse, asEquivalence_functor, ObjectProperty.ι_obj,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply]
  rw [← IsCoverDense.restrictHomEquivHom_symm_apply]
  erw [Equiv.symm_apply_apply]
  erw [CategoryTheory.Adjunction.homEquiv_id]
  rw [toSheafify]
  simp [Adjunction.homEquiv]

variable [HasWeakSheafify K A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify _ _ ≫ ((sheafEquivSheafificationCompatibility J K G A).hom.app F).hom =
      Functor.whiskerLeft G.op (toSheafify _ _) := by
  have := congr($(Adjunction.unit_leftAdjointUniq_hom (sheafifyAdjunctionOfIsEquivalence J K G A)
    (sheafificationAdjunction K A)).app F)
  simp [sheafPushforwardContinuous, sheafEquivSheafificationCompatibility,
    ← whiskerLeft_comp, dsimp% this]

end IsDenseSubsite
end Functor

end CategoryTheory


