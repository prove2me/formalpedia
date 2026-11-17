-- Prove2me | Definitions.Def_QGChasing_Supplement_IsROBDRun
-- name    : QGChasing_Supplement_IsROBDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:25:52.53901+00:00
-- url     : https://prove2.me/theorems/771ab7b0-c315-4647-8ade-2b200def32df
-- title:
--   A run of Regularized Online Balanced Descent (§5.1)
-- statement:
--   Let $X\subseteq\mathbb R^d$, weights $a,b$, hitting costs $f_1,f_2,\dots$, points $v_1,v_2,\dots$ (the minimizers of the $f_t$ over $X$) and a start $x_0$. A sequence $x_0,x_1,\dots$ is a **run of R-OBD** if it starts at $x_0$ and, for every round $t\ge1$, $x_t\in X$ minimizes over $X$
--   $$
--   f_t(x)+\frac a2\|x-x_{t-1}\|^2+\frac b2\|x-v_t\|^2 .
--   $$
--   For convex finite $f_t$, $a,b>0$ and a nonempty closed convex $X$ the minimizer exists and is unique, so the run exists and is unique.
--
--   **Formalization Note** The arg min is a relation (`IsMinOn` over $X$ together with $x_t\in X$). Rounds $t\ge1$ are $t+1$ for $t\in\mathbb N$; $f_0$ and $v_0$ are not used.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), §5.1, p.9 (R-OBD update) with Eq. (5)

import Mathlib

namespace QGChasing.Supplement

/-- `x` is a run of Regularized Online Balanced Descent with weights `a, b` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), §5.1, p.9):
`x 0 = x₀` and, for every round `t ≥ 1`, `x t ∈ X` minimizes over `X`
`f_t(y) + (a/2)‖y − x_{t−1}‖² + (b/2)‖y − v_t‖²`, where `v_t` is the minimizer of `f_t` over `X`.

**Formalization Note** Relational (an `argmin` over `X`, as `IsMinOn`). Round `t` is `t + 1` for
`t : ℕ`; `f 0` and `v 0` are unused. The minimizers `v_t` are passed as a sequence `v`; the theorem
that uses this predicate says what `v_t` is. For convex finite `f_t`, `a, b > 0` and nonempty closed
convex `X` the minimizer exists and is unique (the objective is continuous and `(a + b)`-strongly
convex), so a run exists and is unique. -/
def IsROBDRun {d : ℕ} (a b : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d))
    (x₀ : EuclideanSpace ℝ (Fin d)) (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 0 = x₀ ∧ ∀ t : ℕ, x (t + 1) ∈ X ∧
    IsMinOn (fun y => f (t + 1) y + a / 2 * ‖y - x t‖ ^ 2 + b / 2 * ‖y - v (t + 1)‖ ^ 2) X (x (t + 1))

end QGChasing.Supplement


