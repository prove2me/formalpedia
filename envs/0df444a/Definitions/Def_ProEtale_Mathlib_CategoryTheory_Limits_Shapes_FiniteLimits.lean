-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:39.820912+00:00
-- url     : https://prove2.me/theorems/2e13071b-eb58-4757-a4b5-1915063c6181
-- title:
--   Finite wide pullbacks exist for any finite index type
-- statement:
--   Let $\mathcal C$ be a category with all finite wide pullbacks. Then for every finite type $J$, not necessarily a `Fintype`, $\mathcal C$ has limits of the wide pullback shape indexed by $J$. That shape is a cospan of $J$-many arrows into a common object.
--
--   This instance lets wide pullbacks over arbitrary finite index types, such as finite covers, be formed without first choosing an enumeration.
--
--   **Formalization Note** This is an anonymous instance `HasLimitsOfShape (WidePullbackShape J) C` under `[Finite J] [HasFiniteWidePullbacks C]`. It is obtained by choosing an equivalence `J ≃ Fin n`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/Shapes/FiniteLimits.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace Limits

variable {C : Type*} [Category C]

instance inst_MathlibCategoryTheoryLimitsShapesFiniteLimits_L7 (J : Type*) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  cases nonempty_fintype J
  apply hasLimitsOfShape_of_equivalence
    (WidePullbackShape.equivalenceOfEquiv _ (Fintype.equivFin J).symm)

end Limits
end CategoryTheory


