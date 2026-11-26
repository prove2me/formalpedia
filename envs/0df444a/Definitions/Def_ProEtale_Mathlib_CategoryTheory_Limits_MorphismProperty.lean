-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:17.105345+00:00
-- url     : https://prove2.me/theorems/5b6c8917-073f-5a69-bbe2-8b4ba1acc298
-- title:
--   Closure under pullbacks of objects with structure morphism in P, assuming only base change along the relevant maps
-- statement:
--   Let $P$ be a class of morphisms in a category $\mathcal T$, stable under composition, and suppose $P$ has the *postcomposition cancellation property*: $g \circ f \in P$ and $g \in P$ imply $f \in P$. Fix an object $X$.
--
--   Principal results:
--
--   1. Let $L : \mathcal A \to \mathcal T$ be a functor preserving pullbacks, with $\mathcal A$ and $\mathcal T$ having pullbacks. Consider the costructured arrows $(Y, L(Y) \to X)$ whose structure morphism lies in $P$. Assume that, for any two such objects $Y_1, Y_2$ and every morphism $f : Y_1 \to Y_2$, the class $P$ is stable under base change along $L(f)$. Then these objects are closed under pullbacks, i.e. under limits of cospan shape.
--   2. The special case $L = \mathrm{id}$: if $\mathcal T$ has pullbacks and $P$ is stable under base change along every morphism $f : Y_1 \to Y_2$ of $\mathcal T/X$ between objects with structure morphisms in $P$, then the objects of $\mathcal T/X$ with structure morphism in $P$ are closed under pullbacks.
--
--   These are variants of Mathlib lemmas that need only base-change stability along the legs of the cospans in question, instead of global stability under base change. They apply to classes such as pro-(affine étale) morphisms.
--
--   **Formalization Note** Main declarations: `CostructuredArrow.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong` and `Over.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong`. The conclusion is `IsClosedUnderLimitsOfShape WalkingCospan` for the object properties `P.costructuredArrowObj L` and `P.overObj`. The hypotheses are `P.IsStableUnderComposition`, `P.HasOfPostcompProperty P` and `P.IsStableUnderBaseChangeAlong` for the relevant maps.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/MorphismProperty.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory


open Limits Comma

variable {T : Type*} [Category T] (P : MorphismProperty T)


section CostructuredArrow

variable {A : Type*} [Category A] {L : A ⥤ T}

/-- A variant of `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`
that only requires `P.IsStableUnderBaseChangeAlong` for the cospan legs of each cone, rather
than the global `P.IsStableUnderBaseChange`. -/
lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong
    [HasPullbacks A] [HasPullbacks T] [PreservesLimitsOfShape WalkingCospan L] (X : T)
    [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (hbc : ∀ {Y₁ Y₂ : CostructuredArrow L X} (_ : P Y₁.hom) (_ : P Y₂.hom) (f : Y₁ ⟶ Y₂),
        P.IsStableUnderBaseChangeAlong (L.map f.left)) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <| isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    have hY : Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom := by simp
    have := hbc (hpres .left) (hpres .one) (pres.diag.map WalkingCospan.Hom.inl)
    rw [MorphismProperty.costructuredArrowObj_iff, hY]
    refine P.comp_mem _ _ ?_ (hpres _)
    refine MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback h.flip ?_
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

end CostructuredArrow

section Over

variable {X : T}

/-- A variant of `CategoryTheory.Over.closedUnderLimitsOfShape_pullback` that only requires
`P.IsStableUnderBaseChangeAlong` for the cospan legs of each cone, rather than the global
`P.IsStableUnderBaseChange`. -/
lemma Over.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong [HasPullbacks T]
    [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (hbc : ∀ {Y₁ Y₂ : Over X} (_ : P Y₁.hom) (_ : P Y₂.hom) (f : Y₁ ⟶ Y₂),
        P.IsStableUnderBaseChangeAlong f.left) :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CostructuredArrow.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong (L := 𝟭 T) P X hbc

end Over

end CategoryTheory


