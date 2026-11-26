-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
-- name    : ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:24.597663+00:00
-- url     : https://prove2.me/theorems/9f2bfc11-e8cf-4068-8424-6f254a822c68
-- title:
--   Closure under finite products follows from closure under finite discrete limits in one universe
-- statement:
--   Let $P$ be a property of objects of a category $\mathcal C$.
--
--   **Lemma.** Fix a universe $w$. Suppose that for every finite type $J$ in universe $w$, $P$ is closed under limits of shape $\mathrm{Discrete}(J)$: any limit of a family $(X_j)_{j \in J}$ of objects satisfying $P$ again satisfies $P$. Then $P$ is closed under all finite products, whatever the universe of the indexing type.
--
--   This gives a convenient constructor for the class asserting closure under finite products, so the hypothesis only has to be checked in one universe.
--
--   **Formalization Note** The lemma is `CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape_discrete`. The proof reduces an arbitrary finite index type to `ULift.{w} (Fin n)` through an equivalence of discrete categories.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/ObjectProperty/FiniteProducts.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Additional constructors for `IsClosedUnderFiniteProducts`

We provide a constructor for `IsClosedUnderFiniteProducts`
from `IsClosedUnderLimitsOfShape (Discrete J)` for `(J : Type w) [Finite J]`
in an arbitrary universe `w`.
-/

universe w

namespace CategoryTheory
namespace ObjectProperty

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- To show `P.IsClosedUnderFiniteProducts`, it suffices to show
`P.IsClosedUnderLimitsOfShape (Discrete J)` for all finite `J` in a single universe. -/
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape_discrete
    (h : ∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
    have := h (ULift.{w} (Fin n))
    exact .of_equivalence (Discrete.equivalence (Equiv.ulift.trans e.symm))

end ObjectProperty
end CategoryTheory


