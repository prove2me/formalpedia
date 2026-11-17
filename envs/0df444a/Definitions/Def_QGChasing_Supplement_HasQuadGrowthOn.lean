-- Prove2me | Definitions.Def_QGChasing_Supplement_HasQuadGrowthOn
-- name    : QGChasing_Supplement_HasQuadGrowthOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:24:43.319737+00:00
-- url     : https://prove2.me/theorems/34983250-af4a-4f1b-a527-7afe97ff2686
-- title:
--   $\lambda$-quadratic growth on a set $X$ (Eq. (1), Assumption 4)
-- statement:
--   Let $X\subseteq\mathbb R^d$, $f:\mathbb R^d\to\mathbb R$, $v\in\mathbb R^d$ and $\lambda\in\mathbb R$. The function $f$ has **$\lambda$-quadratic growth at $v$ on $X$** if
--   $$
--   f(x)-f(v)\ \ge\ \frac{\lambda}{2}\,\|x-v\|^2\qquad\text{for all }x\in X .
--   $$
--   This is condition (1) in the form used for squared Euclidean movement, where $v_t$ minimizes $f_t$ over $X$ and the inequality holds on $X$ only (Assumption 4). For $\lambda>0$ and $v\in X$ it makes $v$ the unique minimizer of $f$ over $X$.
--
--   **Formalization Note** The parameter is `lam` in Lean. Membership $v\in X$ is stated separately by the theorems that use the predicate.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (1), p.1, read on X as on p.2; Assumption 4, p.4

import Mathlib

namespace QGChasing.Supplement

/-- `λ`-quadratic growth of `f` at `v` on a set `X` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Eq. (1), p.1, read on `X` as on
p.2, and Assumption 4, p.4): for every `x ∈ X`, `f(x) − f(v) ≥ (λ/2)‖x − v‖²`.

**Formalization Note** The growth parameter is named `lam`. Membership `v ∈ X` is not part of the
predicate; the theorems that use it state `v ∈ X` separately. For `lam > 0` and `v ∈ X` the
inequality makes `v` the unique minimizer of `f` over `X` (Assumption 4's "attains its minimum over
`X` at `v_t`"). -/
def HasQuadGrowthOn {d : ℕ} (lam : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ x ∈ X, lam / 2 * ‖x - v‖ ^ 2 ≤ f x - f v

end QGChasing.Supplement


