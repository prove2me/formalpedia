-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Basic
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:40.941862+00:00
-- url     : https://prove2.me/theorems/68687c2b-84dd-42ab-bb34-5ed25c2b2f0f
-- title:
--   The inverse image of the trivial morphism property is trivial
-- statement:
--   Let $F : \mathcal C \to \mathcal D$ be a functor. The inverse image along $F$ of the morphism property $\top$ on $\mathcal D$, which holds for every morphism, is $\top$ on $\mathcal C$. In other words, every morphism $f$ of $\mathcal C$ satisfies "$F(f)$ is a morphism". The lemma is a simp lemma and holds by definition.
--
--   It simplifies statements about morphism properties pulled back along functors, for example in the definition of sites by classes of morphisms.
--
--   **Formalization Note** The lemma is `CategoryTheory.MorphismProperty.inverseImage_le`. Despite its name, it states the equality `(⊤ : MorphismProperty D).inverseImage F = ⊤`, proved by `rfl`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.MorphismProperty.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open CategoryTheory

@[simp]
lemma CategoryTheory.MorphismProperty.inverseImage_le {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) :
    (⊤ : MorphismProperty D).inverseImage F = ⊤ :=
  rfl


