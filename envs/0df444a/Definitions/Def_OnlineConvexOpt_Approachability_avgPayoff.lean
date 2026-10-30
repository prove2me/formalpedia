-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_avgPayoff
-- name    : OnlineConvexOpt_Approachability_avgPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:40:37.553045+00:00
-- url     : https://prove2.me/theorems/f83f4311-09ca-43ee-8ef9-94f892e81376
-- title:
--   Average payoff vector $\frac1T\sum_{t} u(x_t,y_t)$
-- statement:
--   Given a payoff $u$, an algorithm $\mathcal A$ for the row player and a sequence $y_0,y_1,\dots\in\mathbb R^m$ of column plays, let $x_t=\mathcal A_t(y_0,\dots,y_{t-1})$. The **average payoff after $T$ rounds** is
--
--   $$
--   \bar u_T=\frac1T\sum_{t=0}^{T-1}u(x_t,y_t)\in\mathbb R^d ,
--   $$
--
--   the vector whose distance to $S$ Definition 13.3 requires to vanish.
--
--   **Formalization Note** Rounds are numbered from $0$, so the sum is the book's $\sum_{t=1}^T$. At $T=0$ the value is $0$; it is only used in limits or for $T\ge 1$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Definition 13.3, p. 209 (PDF p. 231)

import Mathlib

namespace OnlineConvexOpt.Approachability

/-- **Average payoff vector after `T` rounds** (the vector of Definition 13.3).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
Definition 13.3, p. 209: "Dist((1/T) Σ_{t=1}^T u(x_t, y_t), S) → 0 as T → ∞", with
"K1 ∋ x_t ← A(y1, y2, . . . , y_{t−1})".

`avgPayoff u A y T = (1/T) ∑_{t<T} u(x_t, y_t)`, where the column player's sequence is
`y : ℕ → ℝ^m` and the row player's play in round `t` is `x_t = A t (y₀, …, y_{t-1})`.

**Formalization Note.** Reading R2: rounds are 0-indexed, so the sum over `t ∈ range T` is the
book's `Σ_{t=1}^T`. At `T = 0` the value is `0` (since `(0 : ℝ)⁻¹ = 0`); every statement of the
mission uses `avgPayoff` only in limits or for `T ≥ 1`. -/
noncomputable def avgPayoff {n m d : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (A : (t : ℕ) → (Fin t → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n))
    (y : ℕ → EuclideanSpace ℝ (Fin m)) (T : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, u (A t (fun i : Fin t => y i)) (y t)

end OnlineConvexOpt.Approachability


