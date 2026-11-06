-- Prove2me | Definitions.Def_QGChasing_IsProxPoint
-- name    : QGChasing_IsProxPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:57.644373+00:00
-- url     : https://prove2.me/theorems/aacf2fe2-2601-456a-a70d-b5eb5c101437
-- title:
--   Proximal point $y(\mu)$ over $X$, Eq. (8)
-- statement:
--   Let $g:\mathbb R^d\to\mathbb R$, $X\subseteq\mathbb R^d$, $p\in\mathbb R^d$ and $\mu\in\mathbb R$. A point $y$ is **the proximal point of $g$ over $X$ around $p$ with parameter $\mu$** if
--   $$
--   y\in\arg\min_{z\in X}\Big(g(z)+\frac{\|z-p\|^2}{2\mu}\Big),
--   $$
--   that is, $y\in X$ and $g(y)+\frac{\|y-p\|^2}{2\mu}\le g(z)+\frac{\|z-p\|^2}{2\mu}$ for every $z\in X$. In Algorithm 1, $g=g_t$, $p=x_{t-1}$ and $y=y_t(\mu)$. For $\mu>0$, $g$ convex and continuous, and $X$ nonempty, closed and convex, the minimizer exists and is unique.
--
--   **Formalization Note** The arg min is a relation.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (8), p.13; also p.6

import Mathlib

namespace QGChasing

/-- `y` is the proximal point `y(μ) = argmin_{z ∈ X} (g(z) + ‖z − p‖²/(2μ))`
(He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (8), p.13; also p.6, with `p = x_{t−1}`): `y ∈ X` and
`g(y) + ‖y − p‖²/(2μ) ≤ g(z) + ‖z − p‖²/(2μ)` for every `z ∈ X`.

**Formalization Note** Relational (an `argmin`). For `μ > 0`, convex continuous `g` and nonempty
closed convex `X` the minimizer exists and is unique (the objective is coercive and
`(1/μ)`-strongly convex, p.13). -/
def IsProxPoint {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) (p : EuclideanSpace ℝ (Fin d)) (μ : ℝ) (y : EuclideanSpace ℝ (Fin d)) : Prop :=
  y ∈ X ∧ ∀ z ∈ X, g y + ‖y - p‖ ^ 2 / (2 * μ) ≤ g z + ‖z - p‖ ^ 2 / (2 * μ)

end QGChasing


