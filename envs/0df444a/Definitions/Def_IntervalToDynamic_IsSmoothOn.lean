-- Prove2me | Definitions.Def_IntervalToDynamic_IsSmoothOn
-- name    : IntervalToDynamic_IsSmoothOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:48.780304+00:00
-- url     : https://prove2.me/theorems/d7246fb2-49c3-4d9a-8493-d4302a735039
-- title:
--   Differentiable and $H$-smooth on a set
-- statement:
--   A function $h$ is differentiable on $\mathcal Y$ with gradient $\nabla h$ and $H$-smooth on $\mathcal Y$ when $\|\nabla h(y)-\nabla h(y')\|_2\le H\|y-y'\|_2$ for every $y,y'\in\mathcal Y$.
--
--   **Formalization Note** In Theorem 6 the function lives on $\mathcal Y$ only, so the gradient is an oracle `gh` with `HasGradientWithinAt h (gh y) Y y`.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 6 (ii), p.10; Lemma 14, p.30

import Mathlib

namespace IntervalToDynamic

/-- `h` is differentiable on `Y` with gradient `gh`, and `H`-smooth on `Y`: the gradient is
`H`-Lipschitz on `Y`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 6 (ii), p.10, and Lemma 14, p.30.

**Formalization Note.** In Theorem 6 the function `h_t` lives on `Y` only, so the gradient is an
oracle within `Y`. -/
def IsSmoothOn {d : ℕ} (Y : Set (EuclideanSpace ℝ (Fin d))) (H : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (gh : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ y ∈ Y, HasGradientWithinAt h (gh y) Y y) ∧
  ∀ y ∈ Y, ∀ y' ∈ Y, ‖gh y - gh y'‖ ≤ H * ‖y - y'‖

end IntervalToDynamic


