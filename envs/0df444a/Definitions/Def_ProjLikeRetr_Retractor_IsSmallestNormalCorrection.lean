-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_IsSmallestNormalCorrection
-- name    : ProjLikeRetr_Retractor_IsSmallestNormalCorrection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:28.935128+00:00
-- url     : https://prove2.me/theorems/2391ec1a-6c81-467d-b385-6ed0465b2814
-- title:
--   Lemma 4.7, p. 17 — smallest normal correction v ∈ N_M(x) with x + u + v ∈ M
-- statement:
--   Let $\mathcal M$ be a subset of a Euclidean space $\mathcal E$ with normal spaces $\mathrm N_{\mathcal M}(x)$, and let $(x,u)\in\mathcal E\times\mathcal E$. A vector $v\in\mathcal E$ is a **smallest normal correction at $(x,u)$** if
--
--   1. $v\in\mathrm N_{\mathcal M}(x)$ and $x+u+v\in\mathcal M$;
--   2. $\|v\|\le\|w\|$ for every $w\in\mathrm N_{\mathcal M}(x)$ with $x+u+w\in\mathcal M$.
--
--   Lemma 4.7 asserts that, near the zero section, there is exactly one such $v$, written $v(x,u)$, and that $R(x,u)=x+u+v(x,u)$ is a retraction (the orthographic retraction).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 17, Lemma 4.7

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Retractor

/-- Lemma 4.7, p. 17: `v` is a smallest normal correction at `(x, u)`: `v ∈ N_M(x)`,
`x + u + v ∈ M`, and `‖v‖ ≤ ‖w‖` for every `w ∈ N_M(x)` with `x + u + w ∈ M`. -/
def IsSmallestNormalCorrection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (p : E × E) (v : E) : Prop :=
  v ∈ normalSpace M p.1 ∧ p.1 + p.2 + v ∈ M ∧
    ∀ w ∈ normalSpace M p.1, p.1 + p.2 + w ∈ M → ‖v‖ ≤ ‖w‖

end ProjLikeRetr.Retractor


