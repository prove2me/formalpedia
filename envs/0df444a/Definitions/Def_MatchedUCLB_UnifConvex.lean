-- Prove2me | Definitions.Def_MatchedUCLB_UnifConvex
-- name    : MatchedUCLB_UnifConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:23.029639+00:00
-- url     : https://prove2.me/theorems/38b9894c-2545-4d09-b0c6-2eec13825d3d
-- title:
--   Uniform convexity of degree $q$ with modulus $\sigma$
-- statement:
--   Let $q,\sigma\in\mathbb R$ and $F:\mathbb R^d\to\mathbb R$. The function $F$ is **uniformly convex of degree $q$ with modulus $\sigma$** if
--
--   $$
--   F(y)\ \ge\ F(x)+\langle\nabla F(x),\,y-x\rangle+\frac{\sigma}{q}\,\|y-x\|^{q}\qquad\text{for all }x,y\in\mathbb R^d .
--   $$
--
--   For $q=2$ this is $\sigma$-strong convexity. It is condition (b) of Theorem 1.1, with the factor $1/q$ of the paper's convention.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and norm. $\langle\nabla F(x),y-x\rangle$ is the Fréchet derivative `fderiv ℝ F x (y - x)`, which Lean sets to $0$ where $F$ is not differentiable; every statement using the predicate also asserts that $F$ is $p$ times continuously differentiable.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Theorem 1.1(b), p.1

import Mathlib

namespace MatchedUCLB

/-- **Uniform convexity of degree `q` with modulus `σ`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Theorem 1.1(b), p.1:
"`F(y) ≥ F(x) + ⟨∇F(x), y − x⟩ + (σ/q)‖y − x‖^q`", for all `x, y ∈ ℝ^d`.

**Formalization Note.** `⟨∇F(x), v⟩` is the Fréchet derivative `fderiv ℝ F x v` (on
`EuclideanSpace ℝ (Fin d)` this is the inner product with the gradient). `‖·‖ ^ q` is
`Real.rpow`. Mathlib's `fderiv` is `0` at points where `F` is not differentiable; every
statement of the mission that uses the predicate also asserts `ContDiff ℝ p F` with `p ≥ 2`. -/
def UnifConvex {d : ℕ} (q σ : ℝ) (F : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin d), F x + fderiv ℝ F x (y - x) + σ / q * ‖y - x‖ ^ q ≤ F y

end MatchedUCLB


