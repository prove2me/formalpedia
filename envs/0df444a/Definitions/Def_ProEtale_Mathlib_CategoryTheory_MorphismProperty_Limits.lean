-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:10.913547+00:00
-- url     : https://prove2.me/theorems/8379edeb-7517-58ab-af46-c947cbfaa60e
-- title:
--   The diagonal of a morphism property containing identities contains identities
-- statement:
--   Let $\mathcal C$ be a category with pullbacks and $P$ a class of morphisms. The *diagonal* property $\Delta P$ holds for $f\colon X \to Y$ when the diagonal morphism $X \to X \times_Y X$ satisfies $P$.
--
--   The file proves: if $P$ contains all identities and is stable under composition with isomorphisms (respects isomorphisms), then $\Delta P$ contains all identities. Indeed, the diagonal of $\mathrm{id}_X$ is an isomorphism $X \to X \times_X X$.
--
--   **Formalization Note** This is an anonymous instance `(MorphismProperty.diagonal P).ContainsIdentities` under `[HasPullbacks C] [P.ContainsIdentities] [P.RespectsIso]`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Limits.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.MorphismProperty.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

open Limits MorphismProperty

instance inst_MathlibCategoryTheoryMorphismPropertyLimits_L7 {C : Type*} [Category C] [HasPullbacks C] (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    (diagonal P).ContainsIdentities where
  id_mem X := by
    change P _
    rw [← Category.id_comp (pullback.diagonal _), P.cancel_right_of_respectsIso]
    exact P.id_mem X


end CategoryTheory


