-- Prove2me | Definitions.Def_HOTrap_HolderClass
-- name    : HOTrap_HolderClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:56.946456+00:00
-- url     : https://prove2.me/theorems/4fd4a9c3-991c-4b6d-9528-c373aabd7cf8
-- title:
--   The Hölder class $C^{p,\beta}(L)$
-- statement:
--   Let $p\ge1$ be an integer, $\beta\in(0,1]$ and $L\ge0$. A function $f:\mathbb R^d\to\mathbb R$ belongs to $C^{p,\beta}(L)$ if $f\in C^p(\mathbb R^d)$ and
--   $$
--   \|\nabla^pf(x)-\nabla^pf(y)\|_{\mathrm{op}}\le L\|x-y\|_2^\beta\qquad\text{for all }x,y\in\mathbb R^d,
--   $$
--   where $\|T\|_{\mathrm{op}}=\sup_{\|v_1\|_2,\dots,\|v_p\|_2\le1}|T[v_1,\dots,v_p]|$.
--
--   This is the smoothness class of the goal theorem; $p+\beta$ is the fractional smoothness order.
--
--   **Formalization Note** $\nabla^pf$ is `iteratedFDeriv ℝ p f`, and the norm of a continuous multilinear map is the operator norm above. The ranges of $p,\beta,L$ are hypotheses of each theorem.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Definition 2.1, p.13

import Mathlib

namespace HOTrap

/-- **The Hölder class `C^{p,β}(L)`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Definition 2.1, p.13: `f : ℝ^d → ℝ` belongs to
`C^{p,β}(L)` if `f ∈ C^p(ℝ^d)` and `∥∇^p f(x) − ∇^p f(y)∥_op ≤ L ∥x − y∥₂^β` for all `x, y ∈ ℝ^d`.

**Formalization Note** `∇^p f` is `iteratedFDeriv ℝ p f`. The norm of a continuous multilinear map is
`sup_{∥v₁∥,…,∥v_p∥ ≤ 1} |T[v₁,…,v_p]|`, which is the paper's `∥·∥_op`. The ranges `p ≥ 1`, `β ∈ (0,1]`,
`L ≥ 0` are hypotheses of each theorem. -/
def HolderClass {d : ℕ} (p : ℕ) (β L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ p f ∧
    ∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖ ^ β

end HOTrap


