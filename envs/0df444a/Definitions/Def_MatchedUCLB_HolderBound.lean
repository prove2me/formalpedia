-- Prove2me | Definitions.Def_MatchedUCLB_HolderBound
-- name    : MatchedUCLB_HolderBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:22.237905+00:00
-- url     : https://prove2.me/theorems/f4e0b757-536d-4f1a-9cb9-8f7132c79804
-- title:
--   pth-order Hölder smoothness $\|\nabla^pF(y)-\nabla^pF(x)\|\le H\|y-x\|^\nu$
-- statement:
--   Let $p\in\mathbb N$, $\nu,H\in\mathbb R$ and $F:\mathbb R^d\to\mathbb R$. The function $F$ has **$p$th-order Hölder smooth derivatives with exponent $\nu$ and parameter $H$** if
--
--   $$
--   \|\nabla^pF(y)-\nabla^pF(x)\|\le H\,\|y-x\|^{\nu}\qquad\text{for all }x,y\in\mathbb R^d .
--   $$
--
--   Here $\nabla^pF(x)$ is the $p$th derivative of $F$ at $x$, a $p$-linear form on $\mathbb R^d$, and the norm of a $k$-linear form $T$ is the operator norm $\|T\|=\sup_{\|z_i\|\le1}|T[z_1,\dots,z_k]|$. This is condition (a) of Theorem 1.1, the smoothness half of the function class.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and norm. $\nabla^pF(x)$ is `iteratedFDeriv ℝ p F x`, whose norm is the operator norm. The predicate does not include differentiability; every statement that uses it also asserts that $F$ is $p$ times continuously differentiable.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Theorem 1.1(a), p.1; Notation, Sec. 3, p.4

import Mathlib

namespace MatchedUCLB

/-- **pth-order Hölder smoothness with exponent `ν` and parameter `H`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Theorem 1.1(a),
p.1: "`‖∇^pF(y) − ∇^pF(x)‖ ≤ H‖y − x‖^ν`", for all `x, y ∈ ℝ^d`; Notation, Sec. 3, p.4: `∇^kF(x)` is
the `k`th derivative of `F` at `x`, and `‖·‖` on `k`-linear forms is the operator norm
`‖T‖ = sup_{‖z_i‖ ≤ 1} |T[z_1, …, z_k]|`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. `∇^pF(x)` is `iteratedFDeriv ℝ p F x`,
a continuous `p`-linear map whose norm is exactly the operator norm of Sec. 3. `‖·‖ ^ ν` is
`Real.rpow`. The predicate does not include `p`-fold differentiability (Mathlib's
`iteratedFDeriv` is `0` where `F` is not differentiable); every statement of the mission that
uses it also asserts `ContDiff ℝ p F`, as Theorem 1.1 asserts that `F` is `p` times
continuously differentiable. -/
def HolderBound {d : ℕ} (p : ℕ) (ν H : ℝ) (F : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin d), ‖iteratedFDeriv ℝ p F y - iteratedFDeriv ℝ p F x‖ ≤ H * ‖y - x‖ ^ ν

end MatchedUCLB


