-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:02.740988+00:00
-- url     : https://prove2.me/theorems/356b5a49-7be3-4279-9eea-c9b9fca750c5
-- title:
--   The one-element cover given by a surjective scheme morphism has a unique index
-- statement:
--   Let $P$ be a morphism property of schemes and $f : X \to S$ a surjective morphism of schemes satisfying $P$. Then $f$ alone forms a $P$-cover of $S$. The file records that the index type of this cover has exactly one element.
--
--   This makes single-morphism covers convenient as covers with a single component, e.g. when describing faithfully flat or pro-étale covers given by one morphism.
--
--   **Formalization Note** The anonymous instance `Unique (f.cover hf).I₀` takes `hf : P f` and `[Surjective f]` and holds because the index type is `PUnit`. The cover `f.cover hf` is the single-morphism cover construction from Mathlib or the fork. I did not inspect its definition beyond the fact that its index type is `PUnit`. Schemes are in universe `u`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

-- `by copilot`


instance inst_MathlibAlgebraicGeometryMorphismsUnderlyingMap_L16 {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] : Unique (f.cover hf).I₀ :=
  inferInstanceAs <| Unique PUnit

end AlgebraicGeometry


