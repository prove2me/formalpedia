-- Prove2me | Definitions.Def_ConeLifts_NonnegRank_slackOperator
-- name    : ConeLifts_NonnegRank_slackOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:09:39.491002+00:00
-- url     : https://prove2.me/theorems/a77c413f-eba5-4dbd-bb61-c763b162d682
-- title:
--   Slack operator $S(x,y) = 1 - \langle x, y\rangle$
-- statement:
--   The operator $S : \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}$ is
--
--   $$S(x, y) = 1 - \langle x, y\rangle .$$
--
--   For a convex body $C \subseteq \mathbb{R}^n$, the **slack operator** $S_C$ is the restriction of $S$ to $\operatorname{ext}(C) \times \operatorname{ext}(C^\circ)$, where $\operatorname{ext}$ denotes the set of extreme points. For a polytope $P$ with the origin in its interior, $\operatorname{ext}(P)$ is the vertex set and $\operatorname{ext}(P^\circ)$ is in bijection with the facets, so $S_P$ is the canonical slack matrix of $P$: its entry at a vertex $v$ and a facet $F$ is the value at $v$ of the facet inequality of $F$ normalized to take the value $1$ at the origin.
--
--   The nonnegative rank and the Boolean rank of a convex body are defined through factorizations of this operator.
--
--   **Formalization Note** The Lean definition is the function $S$ on all of $\mathbb{R}^n \times \mathbb{R}^n$; the restriction to $\operatorname{ext}(C) \times \operatorname{ext}(C^\circ)$ is made in every definition and theorem that uses it, by quantifying over `Set.extremePoints ℝ C` and `Set.extremePoints ℝ (polar C)`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 (slack operator); p. 9, §3 (slack operator of a polytope = canonical slack matrix)

import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.NonnegRank

/-- The operator `S : ℝⁿ × ℝⁿ → ℝ`, `S(x, y) = 1 − ⟨x, y⟩` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §2, p. 3). The **slack operator** `S_C` of a convex body `C` is its restriction
to `ext(C) × ext(C°)`; every statement of this mission evaluates `slackOperator x y` only for
`x ∈ Set.extremePoints ℝ C` and `y ∈ Set.extremePoints ℝ (polar C)`. For a polytope with the origin
in its interior this is the canonical slack matrix (§3, p. 9). -/
noncomputable def slackOperator {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 - ⟪x, y⟫_ℝ

end ConeLifts.NonnegRank


