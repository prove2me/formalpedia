-- Prove2me | Definitions.Def_SuperPolyak_solutionSet
-- name    : SuperPolyak_solutionSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:59.468985+00:00
-- url     : https://prove2.me/theorems/bc701d54-2c34-47ad-8379-2ef5d4175282
-- title:
--   Solution set $X^*=\operatorname{argmin} f$ and the projection map $P_X(x)$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$. Its **solution set** is the set of global minimizers
--   $$
--   X^*=\operatorname*{argmin}_{x\in\mathbb R^d} f(x)=\{x\in\mathbb R^d:\ f(x)\le f(y)\ \text{for all } y\in\mathbb R^d\}.
--   $$
--   For a set $X\subseteq\mathbb R^d$ and a point $x$, the **projection map** is the set of nearest points
--   $$
--   P_X(x)=\operatorname*{argmin}_{y\in X}\|y-x\|=\{y\in X:\ \|y-x\|\le\|z-x\|\ \text{for all } z\in X\}.
--   $$
--   The distance $\operatorname{dist}(x,X)=\inf_{y\in X}\|y-x\|$ is the usual infimum distance.
--
--   Every statement of the mission measures progress through $\operatorname{dist}(x,X^*)$ and through nearest points $\hat x\in P_{X^*}(x)$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. $P_X(x)$ is a set, possibly empty for an arbitrary $X$; the distance is Mathlib's `Metric.infDist`. When $\bar x\in X^*$, the optimal value $f^*$ is $f(\bar x)$.
-- source:
--   Charisopoulos & Davis, A superlinearly convergent subgradient method for sharp semismooth problems, arXiv:2201.04611v1, §1.1, p.5 (dist and P_X) and §2, display (6), p.7 (X* = argmin f)

import Mathlib

namespace SuperPolyak

/-- **Solution set** `X* = argmin_{x ∈ ℝᵈ} f(x)` (Charisopoulos & Davis, *A superlinearly
convergent subgradient method for sharp semismooth problems*, arXiv:2201.04611v1, §2, display (6),
p.7): the set of global minimizers of `f : ℝᵈ → ℝ`.

**Formalization Note** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`. When `x̄ ∈ X*`, the optimal value
`f*` of the paper is `f x̄`; the mission's statements write `f x̄` for `f*`. -/
def solutionSet {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ y, f x ≤ f y}

/-- **Projection map** `P_X(x) := argmin_{y ∈ X} ‖y − x‖` (arXiv:2201.04611v1, §1.1, p.5): the
*set* of nearest points of `X` to `x`. The paper's "`x̂ ∈ P_{X*}(x)`" means any such nearest point.

**Formalization Note** The distance `dist(x, X) := inf_{y ∈ X} ‖y − x‖` of the same paragraph is
Mathlib's `Metric.infDist x X`. For a nonempty closed set in `ℝᵈ` the set `P_X(x)` is nonempty;
for an arbitrary set it may be empty, and no statement of the mission asserts that it is not. -/
def nearestPoints {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ X ∧ ∀ z ∈ X, ‖y - x‖ ≤ ‖z - x‖}

end SuperPolyak


