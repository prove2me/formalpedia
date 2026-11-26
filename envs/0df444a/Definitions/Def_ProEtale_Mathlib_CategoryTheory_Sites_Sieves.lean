-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_Sieves
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:41.145566+00:00
-- url     : https://prove2.me/theorems/cfe3579c-7b58-4932-8fc9-1746d032ddb8
-- title:
--   Presieves: uncurrying joins and meets, and images under composite functors
-- statement:
--   For an object $X$ of a category $\mathcal C$, a presieve $R$ on $X$ is a family of morphisms with target $X$. Its "uncurried" form is the corresponding set of pairs $(Y, g\colon Y \to X)$.
--
--   Results:
--
--   1. For presieves $R, S$ on $X$, the uncurried form of $R \sqcup S$ is the union of the uncurried forms, and that of $R \sqcap S$ is their intersection.
--   2. For functors $F\colon \mathcal C \to \mathcal D$ and $G\colon \mathcal D \to \mathcal E$, the image of a presieve under the composite is the iterated image:
--   $$R.\mathrm{map}(G \circ F) = (R.\mathrm{map}\,F).\mathrm{map}\,G.$$
--
--   These are bookkeeping lemmas for manipulating covering families in the sites used later.
--
--   **Formalization Note** The declarations are `CategoryTheory.Presieve.uncurry_sup`, `Presieve.uncurry_inf` (both by `rfl`) and the simp lemma `Presieve.map_comp`, written `R.map (F ⋙ G) = (R.map F).map G`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/Sieves.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.Sieves

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Presieve.uncurry_sup {X : C} (R S : Presieve X) :
    (R ⊔ S).uncurry = R.uncurry ∪ S.uncurry := rfl

lemma Presieve.uncurry_inf {X : C} (R S : Presieve X) :
    (R ⊓ S).uncurry = R.uncurry ∩ S.uncurry := rfl

@[simp]
lemma Presieve.map_comp {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm ?_ ?_
  · rw [Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    apply Presieve.map_map
    exact hf
  · rw [Presieve.map_le_iff_le_functorPullback, Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    exact hf


end CategoryTheory


