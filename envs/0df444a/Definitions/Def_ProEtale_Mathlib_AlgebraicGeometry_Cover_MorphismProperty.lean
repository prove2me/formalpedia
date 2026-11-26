-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:56.938386+00:00
-- url     : https://prove2.me/theorems/7f88d400-2e52-47f0-8ea1-7bab4285efab
-- title:
--   Weakening the morphism property of a cover of a scheme
-- statement:
--   For a morphism property $P$ of schemes, a $P$-cover of a scheme $S$ is a family of morphisms $(U_i \to S)_i$ in $P$ that is jointly surjective. The file defines the weakening of covers: if $P \le Q$ (every morphism in $P$ is in $Q$), then every $P$-cover $\mathcal U$ of $S$ is also a $Q$-cover of $S$, with the same objects and maps.
--
--   This is used to regard, for instance, étale covers as weakly étale covers, i.e. to pass from the étale to the pro-étale site.
--
--   **Formalization Note** The construction is `AlgebraicGeometry.Scheme.Cover.weaken` (an `abbrev`), taking `hPQ : P ≤ Q` and `𝒰 : Cover.{v} (precoverage P) S` and returning `S.Cover (precoverage Q)`; its underlying pre-zero-hypercover is that of $\mathcal U$ (a `simps` lemma records this).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Cover/MorphismProperty.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

@[simps toPreZeroHypercover]
abbrev Scheme.Cover.weaken {Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q)
    (𝒰 : Cover.{v} (precoverage P) S) :
    S.Cover (precoverage Q) where
  __ := 𝒰
  mem₀ := by
    rw [ofArrows_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      exact 𝒰.exists_eq x
    · intro i
      apply hPQ
      exact 𝒰.map_prop i

end AlgebraicGeometry


