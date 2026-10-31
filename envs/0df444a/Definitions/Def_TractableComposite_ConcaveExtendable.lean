-- Prove2me | Definitions.Def_TractableComposite_ConcaveExtendable
-- name    : TractableComposite_ConcaveExtendable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:42.530566+00:00
-- url     : https://prove2.me/theorems/fb10382b-58f9-454d-8a17-7ff788fc09f3
-- title:
--   Concave-extendability from a subset
-- statement:
--   A function $g:D\to\mathbb R$ on a polytope $D$ is concave-extendable from $X\subseteq D$ if the concave envelope of $g$ is determined by $X$ only: the concave envelopes of $g$ and of $g|_X$ over $D$ agree,
--
--   $$\operatorname{conc}_D(g)(x)=\operatorname{conc}_D(g|_X)(x)\qquad\text{for all }x\in D.$$
--
--   **Formalization Note.** The printed definition says "over $P$"; it means over $D$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Definition 1, p.6

import Mathlib
import Definitions.Def_TractableComposite_concOn

namespace TractableComposite

/-- **Concave-extendability**, Definition 1, p.6: a function `g : D → ℝ` on a polytope `D` is
concave-extendable from `X ⊆ D` if the concave envelopes of `g` and of `g|_X` over `D` are identical.
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Definition 1, p.6.

**Formalization Note.** Reading R7: the printed "over P" is a typo for "over D". The envelope of `g|_X`
over `D` is `concOn X g` (see `concOn`); the identity is required at every point of `D`. -/
def ConcaveExtendable {E : Type*} [AddCommGroup E] [Module ℝ E] (D X : Set E) (g : E → ℝ) : Prop :=
  ∀ x ∈ D, concOn D g x = concOn X g x

end TractableComposite


