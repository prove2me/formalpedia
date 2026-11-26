-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Comma
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_Comma
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:27.645502+00:00
-- url     : https://prove2.me/theorems/30dd335a-b2df-4993-948d-7cbece696670
-- title:
--   The projections from a comma category preserve limits of a given shape
-- statement:
--   Let $L : A \to T$ and $R : B \to T$ be functors and $(L \downarrow R)$ their comma category, with objects $(a, b, L a \to R b)$. Let $J$ be a category such that $A$ and $B$ have limits of shape $J$ and $R$ preserves them. Then both projections
--   $$\mathrm{fst} : (L \downarrow R) \to A, \qquad \mathrm{snd} : (L \downarrow R) \to B$$
--   preserve limits of shape $J$.
--
--   In particular, limits in over categories and in categories of morphisms with a property, built as comma categories, are computed on the underlying objects.
--
--   **Formalization Note** The instances are `CategoryTheory.Comma.preservesLimitsOfShape_fst` and `CategoryTheory.Comma.preservesLimitsOfShape_snd`. They use Mathlib's construction of limits in `Comma L R` from limits in `A` and `B` when `R` preserves them. The file states no hypothesis on $L$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/Comma.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Limits.Comma

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

open Limits

variable {A B T : Type*} [Category A] [Category B] [Category T]
  (L : A ⥤ T) (R : B ⥤ T)
variable {J : Type*} [Category J]

namespace Comma

instance preservesLimitsOfShape_fst [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : PreservesLimitsOfShape J (Comma.fst L R) where
  preservesLimit :=
    preservesLimit_of_preserves_limit_cone
      (coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

instance preservesLimitsOfShape_snd [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : PreservesLimitsOfShape J (Comma.snd L R) where
  preservesLimit :=
    preservesLimit_of_preserves_limit_cone
      (coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

end Comma

end CategoryTheory


