-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sheafification
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_Sheafification
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:35.612261+00:00
-- url     : https://prove2.me/theorems/6ffb6c88-1c06-593b-aa98-6b52e9ab12ad
-- title:
--   Sheafifying a diagram of sheaves returns the diagram up to natural isomorphism
-- statement:
--   Let $C$ be a category with a Grothendieck topology $J$, and $\mathcal A$ a category in which $J$-sheafification exists. Let $G : I \to \mathrm{PSh}(C,\mathcal A)$ be a diagram of presheaves such that each $G(i)$ is a $J$-sheaf. Then sheafifying $G$ and forgetting back to presheaves gives a functor naturally isomorphic to $G$:
--   $$\iota \circ a \circ G \;\cong\; G,$$
--   where $a$ is sheafification and $\iota$ the inclusion of sheaves into presheaves. The components are the inverses of the canonical isomorphisms $G(i) \cong \iota a G(i)$.
--
--   This is used to compute colimits or limits of sheaves via presheaves.
--
--   **Formalization Note** The definition is `CategoryTheory.presheafToSheafSheafToPresheafIso`, assuming `[HasWeakSheafify J A]` and a hypothesis `H : ∀ i, Presheaf.IsSheaf J (G.obj i)`. Its type is `G ⋙ presheafToSheaf J A ⋙ sheafToPresheaf J A ≅ G`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/Sheafification.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.Sheafification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

/-- If `G : I ⥤ (Cᵒᵖ ⥤ A)` takes values in `J`-sheafs, the post-composition with
sheafification and inclusion is isomorphic to `G`. -/
noncomputable
def presheafToSheafSheafToPresheafIso {C I A : Type*} [Category* C]
    [Category* I] [Category* A] (J : GrothendieckTopology C) [HasWeakSheafify J A]
    (G : I ⥤ (Cᵒᵖ ⥤ A)) (H : ∀ (i : I), Presheaf.IsSheaf J (G.obj i)) :
    G ⋙ presheafToSheaf J A ⋙ sheafToPresheaf J A ≅ G :=
  NatIso.ofComponents (fun i ↦ (isoSheafify _ (H _)).symm) <| by
    intro i j u
    apply sheafify_hom_ext _ _ _ (H _)
    simp

end CategoryTheory


