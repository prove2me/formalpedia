-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_IsApproachabilityAlg
-- name    : OnlineConvexOpt_Approachability_IsApproachabilityAlg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:40:15.772504+00:00
-- url     : https://prove2.me/theorems/38752f56-5871-4cb5-b264-2d83e9f499e1
-- title:
--   Approachability algorithm playing in $\mathcal K_1$
-- statement:
--   An **algorithm for the row player** maps each round $t=0,1,2,\dots$ and each history $(y_0,\dots,y_{t-1})\in(\mathbb R^m)^t$ of the column player's past plays to a point $\mathcal A_t(y_0,\dots,y_{t-1})\in\mathbb R^n$. It is **admissible** for the decision sets $\mathcal K_1,\mathcal K_2$ if
--
--   $$
--   y_0,\dots,y_{t-1}\in\mathcal K_2\ \Longrightarrow\ \mathcal A_t(y_0,\dots,y_{t-1})\in\mathcal K_1 \qquad\text{for every } t .
--   $$
--
--   These are the algorithms $\mathcal K_1\ni x_t\leftarrow\mathcal A(y_1,\dots,y_{t-1})$ of Definition 13.3.
--
--   **Formalization Note** Rounds are numbered from $0$: the book's $x_t$, $t\ge 1$, is the play in round $t-1$ here. The algorithm is deterministic and does not know the horizon.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Definition 13.3, p. 209 (PDF p. 231)

import Mathlib

namespace OnlineConvexOpt.Approachability

/-- **An algorithm for the row player** (the algorithms of Definition 13.3).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
Definition 13.3, p. 209: "… some algorithm A, called an approachability algorithm, which
iteratively selects points K1 ∋ x_t ← A(y1, y2, . . . , y_{t−1}) …".

An algorithm is a family `A t h`, where `t : ℕ` is the round (0-indexed) and `h : Fin t → ℝ^m`
is the history `y₀, …, y_{t-1}` of the column player's past plays. `IsApproachabilityAlg K₁ K₂ A`
says that on every history whose entries lie in `K₂` the algorithm plays a point of `K₁`.

**Formalization Note.** Reading R2: rounds are 0-indexed; the book's `x_t`, `t = 1, 2, …` is
`A (t-1) (y₀, …, y_{t-2})` here. The algorithm is deterministic and does not know the horizon.
Without the membership requirement every set would be approachable (play points outside `K₁`). -/
def IsApproachabilityAlg {n m : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (A : (t : ℕ) → (Fin t → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (t : ℕ) (h : Fin t → EuclideanSpace ℝ (Fin m)), (∀ i, h i ∈ K₂) → A t h ∈ K₁

end OnlineConvexOpt.Approachability


