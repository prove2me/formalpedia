-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:29.516148+00:00
-- url     : https://prove2.me/theorems/8e087b1f-7cf0-527e-bc81-c3d32e4c990c
-- title:
--   Morphisms with prescribed source and target properties are stable under composition
-- statement:
--   This file continues the published file of the same name. For object properties $P, Q$ of a category $\mathcal C$, the morphism property determined by them holds for $f : X \to Y$ iff $X$ satisfies $P$ and $Y$ satisfies $Q$. The file proves that this morphism property is stable under composition: if $f : X \to Y$ and $g : Y \to Z$ satisfy it, then $X$ satisfies $P$ and $Z$ satisfies $Q$, so $g \circ f$ does too.
--
--   **Formalization Note** The result is an unnamed instance `(MorphismProperty.ofObjectProperty P Q).IsStableUnderComposition`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/OfObjectProperty.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty of the same module.

import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace MorphismProperty


instance inst_MathlibCategoryTheoryMorphismPropertyOfObjectProperty_L17 {C : Type*} [Category* C] (P Q : ObjectProperty C) :
    (ofObjectProperty P Q).IsStableUnderComposition where
  comp_mem _ _ hf hg := ⟨hf.left, hg.right⟩

end MorphismProperty
end CategoryTheory


