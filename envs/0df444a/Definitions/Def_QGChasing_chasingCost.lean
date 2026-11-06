-- Prove2me | Definitions.Def_QGChasing_chasingCost
-- name    : QGChasing_chasingCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:59.602734+00:00
-- url     : https://prove2.me/theorems/738a138a-5c39-4c61-a997-c14dc1f0b566
-- title:
--   Total cost $\sum_{t=1}^T (f_t(x_t)+\|x_t-x_{t-1}\|)$
-- statement:
--   For hitting costs $f_1,f_2,\dots$ on $\mathbb R^d$, a decision sequence $x_0,x_1,\dots$ and a horizon $T$, the **total cost under Euclidean movement** is
--   $$
--   \mathrm{cost}_T(x)=\sum_{t=1}^{T}\big(f_t(x_t)+\|x_t-x_{t-1}\|\big).
--   $$
--   It is the numerator of the competitive ratio for the learner's decisions and its denominator for an offline comparator sequence.
--
--   **Formalization Note** Rounds $1,\dots,T$ are $t+1$ for $t\in\{0,\dots,T-1\}$; $f_0$ is not used.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), p.1 (definition of CR, with m(x, y) = ‖x − y‖)

import Mathlib

namespace QGChasing

/-- The total cost `∑_{t=1}^T (f_t(x_t) + ‖x_t − x_{t−1}‖)` of a decision sequence `x₀, x₁, …`
under hitting costs `f₁, f₂, …` and Euclidean movement `m(x, y) = ‖x − y‖` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.1, the
numerator and denominator of `CR`).

**Formalization Note** Rounds `1, …, T` are `t + 1` for `t ∈ Finset.range T`; `f 0` is not used. -/
noncomputable def chasingCost {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (f (t + 1) (x (t + 1)) + ‖x (t + 1) - x t‖)

end QGChasing


