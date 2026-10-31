-- Prove2me | Definitions.Def_TensorAHPE_IsApproxSol
-- name    : TensorAHPE_IsApproxSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:55.696278+00:00
-- url     : https://prove2.me/theorems/2538b4f4-198c-41d6-a784-a3db8af8be8d
-- title:
--   $\hat\sigma$-approximate solution of the subproblem (2.5) (Definition 2.1)
-- statement:
--   Fix $f$, $h$, an order $d$, a regularization parameter $M$, and let $f_x$ be the model (2.4). The proximal tensor subproblem at $(\lambda,x)$ is
--
--   $$\min_{y\in\mathbb R^n} f_x(y) + h(y) + \frac1{2\lambda}\|y-x\|^2. \qquad (2.5)$$
--
--   Given $(\lambda,x)\in\mathbb R_{++}\times\mathbb R^n$ and $\hat\sigma\ge0$, a triple $(y,u,\epsilon)\in\mathbb R^n\times\mathbb R^n\times\mathbb R_+$ is a **$\hat\sigma$-approximate solution of (2.5) at $(\lambda,x)$** if
--
--   $$u \in (\nabla f_x + \partial_\epsilon h)(y) \quad\text{and}\quad \|\lambda u + y - x\|^2 + 2\lambda\epsilon \le \hat\sigma^2\|y-x\|^2. \qquad (2.7)$$
--
--   The exact solution $y$ of (2.5) with $u$ from its optimality condition gives $(y,u,0)$, an approximate solution for every $\hat\sigma\ge0$. Algorithm 2 calls a subroutine returning such a triple in each iteration.
--
--   **Formalization Note** The inclusion is written $u-\nabla f_x(y)\in\partial_\epsilon h(y)$, with $\nabla f_x$ Mathlib's `gradient` of the real function $f_x$ (differentiable for $d\ge1$). The conditions $\lambda>0$, $\hat\sigma\ge0$, $\epsilon\ge0$ are part of the definition.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Definition 2.1, p.6 (with (2.5), p.5)

import Mathlib
import Definitions.Def_TensorAHPE_epsSubdiff
import Definitions.Def_TensorAHPE_model

namespace TensorAHPE

/-- **σ̂-approximate solution of the subproblem (2.5)** (Definition 2.1).
Jiang, Wang & Zhang, arXiv:1812.06557v3, Definition 2.1, p.6: "Given (λ, x) ∈ ℝ₊₊ × ℝⁿ and
σ̂ ≥ 0, the triplet (y, u, ε) ∈ ℝⁿ × ℝⁿ × ℝ₊ is called a σ̂-approximate solution of (2.5) at
(λ, x) if u ∈ (∇f_x + ∂_ε h)(y) and ‖λu + y − x‖² + 2λε ≤ σ̂²‖y − x‖². (2.7)"
The subproblem (2.5), p.5, is `min_y f_x(y) + h(y) + (1/2λ)‖y − x‖²`.

`IsApproxSol f h d M σ̂ λ x y u ε` holds when `λ > 0`, `σ̂ ≥ 0`, `ε ≥ 0`,
`u − ∇f_x(y) ∈ ∂_ε h(y)`, and (2.7) holds, where `f_x = model f d M x` is (2.4).

**Formalization Note.** `u ∈ (∇f_x + ∂_ε h)(y)` is written `u − ∇f_x(y) ∈ ∂_ε h(y)`. The gradient
`∇f_x(y)` is Mathlib's `gradient` of the real function `model f d M x`; for `d ≥ 1` that function
is differentiable, so the gradient is the true one. -/
def IsApproxSol {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin n) → EReal)
    (d : ℕ) (M σhat lam : ℝ) (x y u : EuclideanSpace ℝ (Fin n)) (ε : ℝ) : Prop :=
  0 < lam ∧ 0 ≤ σhat ∧ 0 ≤ ε ∧
    u - gradient (model f d M x) y ∈ epsSubdiff h ε y ∧
    ‖lam • u + y - x‖ ^ 2 + 2 * lam * ε ≤ σhat ^ 2 * ‖y - x‖ ^ 2

end TensorAHPE


