-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Pullback
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_Pullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:08.831089+00:00
-- url     : https://prove2.me/theorems/44aab1b2-2f6d-59fe-94f7-d8d115efebf4
-- title:
--   Sheaf pullback along a continuous functor as sheafified left Kan extension
-- statement:
--   Let $F\colon \mathcal C \to \mathcal D$ be a functor that is continuous for Grothendieck topologies $J$ on $\mathcal C$ and $K$ on $\mathcal D$, and let $\mathcal A$ be a coefficient category. Then $F$ induces a pushforward functor $F_*\colon \mathrm{Sh}(\mathcal D, K; \mathcal A) \to \mathrm{Sh}(\mathcal C, J; \mathcal A)$, $G \mapsto G \circ F^{\mathrm{op}}$, and its left adjoint, the pullback $F^*$.
--
--   Assume that sheafification exists for $K$ and that every presheaf on $\mathcal C$ has a left Kan extension along $F^{\mathrm{op}}$. The file gives the natural isomorphism
--   $$F^* \;\cong\; (\,\cdot\,)^{\#}_K \circ \operatorname{Lan}_{F^{\mathrm{op}}} \circ \iota_J,$$
--   where $\iota_J$ is the inclusion of $J$-sheaves into presheaves and $(\,\cdot\,)^{\#}_K$ is $K$-sheafification;
--   that is, $F^*G \cong (\operatorname{Lan}_{F^{\mathrm{op}}} G)^{\#}$.
--
--   Routine results:
--
--   1. The underlying presheaf map of $F_*(\varphi)$ is $\varphi$ whiskered by $F^{\mathrm{op}}$, and the forgetful functor to presheaves sends a sheaf map to its underlying presheaf map.
--   2. Compatibility of the adjunction unit $G \to F_*F^*G$ with this description, in both directions of the isomorphism and componentwise. The unit composed with the isomorphism equals the Kan extension unit followed by the sheafification map.
--
--   This gives a concrete formula for the pullback of sheaves, used to compare sheaves on different sites.
--
--   **Formalization Note** The declarations are `Functor.sheafPushforwardContinuous_map_hom`, `Functor.sheafPullbackIso : F.sheafPullback A J K ≅ sheafToPresheaf J A ⋙ F.op.lan ⋙ presheafToSheaf K A` (under `[HasWeakSheafify K A]` and `[∀ G, F.op.HasLeftKanExtension G]`), `sheafToPresheaf_map`, `Functor.sheafAdjunctionContinuous_unit_app_hom_sheafPullbackIso_hom`, `Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom` and its componentwise variant `..._app`. The isomorphism is obtained from Mathlib's `Functor.sheafPullbackConstruction`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/Pullback.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.Pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]

@[simp]
lemma Functor.sheafPushforwardContinuous_map_hom {G G' : Sheaf K A} (f : G ⟶ G') :
    ((F.sheafPushforwardContinuous A J K).map f).hom = F.op.whiskerLeft f.hom :=
  rfl

variable [HasWeakSheafify K A] [∀ (G : Cᵒᵖ ⥤ A), F.op.HasLeftKanExtension G]

/-- If left Kan extensions along `F : C ⥤ D` exist and `D` has sheafification,
the sheaf pullback can be computed as the sheafification of the left Kan extension. -/
noncomputable
def Functor.sheafPullbackIso :
    F.sheafPullback A J K ≅ sheafToPresheaf J A ⋙ F.op.lan ⋙ presheafToSheaf K A :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

-- TODO: move
lemma sheafToPresheaf_map {F G : Sheaf J A} (f : F ⟶ G) :
    (sheafToPresheaf _ _).map f = f.hom := by
  simp

@[reassoc (attr := simp)]
lemma Functor.sheafAdjunctionContinuous_unit_app_hom_sheafPullbackIso_hom
    (G : Sheaf J A) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom ≫
      F.op.whiskerLeft ((F.sheafPullbackIso A J K).hom.app G).hom =
      (F.op.lanUnit.app G.obj) ≫
      F.op.whiskerLeft (toSheafify K (F.op.leftKanExtension G.obj)) := by
  dsimp [Functor.sheafPullbackIso, Functor.sheafPullbackConstruction.sheafPullbackIso]
  have := congr(($(Adjunction.unit_leftAdjointUniq_hom (F.sheafAdjunctionContinuous A J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)).app G).hom)
  dsimp at this
  rw [this]
  dsimp [sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.lan]

@[reassoc (attr := simp)]
lemma Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom
    (G : Sheaf J A) :
    F.op.lanUnit.app G.obj ≫
      F.op.whiskerLeft (toSheafify K (F.op.leftKanExtension G.obj)) ≫
      F.op.whiskerLeft ((F.sheafPullbackIso A J K).inv.app G).hom =
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom := by
  rw [← cancel_mono (F.op.whiskerLeft ((F.sheafPullbackIso A J K).hom.app G).hom)]
  simp [← Functor.whiskerLeft_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    sheafify, Functor.lan]

@[reassoc (attr := simp)]
lemma Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom_app
    (G : Sheaf J A) (U : Cᵒᵖ) :
    dsimp% (F.op.lanUnit.app G.obj).app U ≫
      (toSheafify K (F.op.leftKanExtension G.obj)).app (Opposite.op (F.obj U.unop)) ≫
        ((F.sheafPullbackIso A J K).inv.app G).hom.app (Opposite.op (F.obj U.unop)) =
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app U := by
  rw [← Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom]
  rfl

end CategoryTheory


