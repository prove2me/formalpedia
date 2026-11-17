-- Prove2me | Definitions.Def_QGChasing_Supplement_sqCost
-- name    : QGChasing_Supplement_sqCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:26:08.423686+00:00
-- url     : https://prove2.me/theorems/3d374a5d-2649-4e84-a038-f8c2859ec75c
-- title:
--   Total cost under squared Euclidean movement
-- statement:
--   For hitting costs $f_1,f_2,\dots$, a decision sequence $x_0,x_1,\dots$ and a horizon $T$, the total cost with squared Euclidean movement $m(x,y)=\frac12\|x-y\|^2$ is
--   $$
--   \sum_{t=1}^T\Big(f_t(x_t)+\frac12\|x_t-x_{t-1}\|^2\Big).
--   $$
--   It is the numerator of the competitive ratio for the online path and, minimized over comparator paths, its denominator.
--
--   **Formalization Note** Rounds $1,\dots,T$ are $t+1$ for $t\in\{0,\dots,T-1\}$; $f_0$ is not used.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), p.1 (definition of CR with m(x, y) = ½‖x − y‖²); p.20 (cost)

import Mathlib

namespace QGChasing.Supplement

/-- The total cost `∑_{t=1}^T (f_t(x_t) + ½‖x_t − x_{t−1}‖²)` of a decision sequence under hitting
costs `f₁, f₂, …` and squared Euclidean movement `m(x, y) = ½‖x − y‖²` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.1, the numerator
and denominator of `CR`; p.20, `cost(x_t)`).

**Formalization Note** Rounds `1, …, T` are `t + 1` for `t ∈ Finset.range T`; `f 0` is unused (the
convention of the base mission's `QGChasing.chasingCost`). -/
noncomputable def sqCost {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (f (t + 1) (x (t + 1)) + 1 / 2 * ‖x (t + 1) - x t‖ ^ 2)

end QGChasing.Supplement


