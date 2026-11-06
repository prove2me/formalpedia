-- Prove2me | Definitions.Def_QGChasing_HasQuadGrowth
-- name    : QGChasing_HasQuadGrowth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:54.760317+00:00
-- url     : https://prove2.me/theorems/e6f9ec05-e879-49dd-a1ff-2cdbde5015b3
-- title:
--   $\lambda$-quadratic growth at a point, Eq. (1)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, $v\in\mathbb R^d$ and $\lambda\in\mathbb R$. The function $f$ has **$\lambda$-quadratic growth at $v$** if
--   $$
--   f(x)-f(v)\ \ge\ \frac{\lambda}{2}\,\|x-v\|^2\qquad\text{for all }x\in\mathbb R^d .
--   $$
--   This is the condition (1) in the form used for Euclidean movement, where it holds on the whole space and $v$ is a global minimizer (Assumption 3). For $\lambda>0$ it forces $v$ to be the unique global minimizer of $f$.
--
--   **Formalization Note** The parameter is called `lam` in Lean, because `λ` is reserved.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (1), p.1, and p.2; Assumption 3, p.4

import Mathlib

namespace QGChasing

/-- `λ`-quadratic growth of `f` at the point `v` on all of `ℝᵈ` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (1), p.1, and
Assumption 3, p.4): for every `x ∈ ℝᵈ`,
`f(x) − f(v) ≥ (λ/2)‖x − v‖²`.

**Formalization Note** The growth parameter is named `lam` (`λ` is not a Lean identifier). The
inequality is required on the whole space (the Euclidean-movement reading of (1), p.2: "`v_t` is a
global minimizer and the condition holds on `ℝᵈ`"). For `lam > 0` it makes `v` the unique global
minimizer of `f`. -/
def HasQuadGrowth {d : ℕ} (lam : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin d), lam / 2 * ‖x - v‖ ^ 2 ≤ f x - f v

end QGChasing


