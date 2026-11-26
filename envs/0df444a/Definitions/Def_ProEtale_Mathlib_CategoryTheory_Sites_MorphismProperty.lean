-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_MorphismProperty
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_MorphismProperty
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:55.020994+00:00
-- url     : https://prove2.me/theorems/efcb92e0-4212-4f61-9133-449ffd9544d5
-- title:
--   Singleton presieves in the precoverage of a morphism property, and stability of that precoverage under unions
-- statement:
--   For a class $P$ of morphisms in a category $\mathcal C$, the precoverage associated with $P$ declares a presieve on $Y$ covering when all its arrows lie in $P$.
--
--   Principal results:
--   1. For $f : X \to Y$, the singleton presieve $\{f\}$ is in the $P$-precoverage of $Y$ if and only if $f \in P$.
--   2. The $P$-precoverage is stable under unions of presieves: if two presieves on $Y$ are covering, so is their union.
--
--   These are small helpers for building topologies on sites from morphism properties.
--
--   **Formalization Note** Declarations: `CategoryTheory.MorphismProperty.singleton_mem_precoverage_iff` (a simp lemma) and an unnamed instance `P.precoverage.IsStableUnderSup`, for Mathlib's `MorphismProperty.precoverage`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/MorphismProperty.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.MorphismProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace MorphismProperty

variable {C : Type*} [Category C] {P : MorphismProperty C}

@[simp]
lemma singleton_mem_precoverage_iff {X Y : C} {f : X ⟶ Y} :
    Presieve.singleton f ∈ P.precoverage Y ↔ P f := by
  simp [← Presieve.ofArrows_pUnit.{0}]

instance inst_MathlibCategoryTheorySitesMorphismProperty_L12 : P.precoverage.IsStableUnderSup where
  sup_mem_coverings hR hS Y f hf := by
    obtain (h|h) := hf
    · exact hR h
    · exact hS h

end MorphismProperty
end CategoryTheory


