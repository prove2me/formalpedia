-- Prove2me | Definitions.Def_TensorAHPE_model
-- name    : TensorAHPE_model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:24.140972+00:00
-- url     : https://prove2.me/theorems/71da6e37-bdd3-40c7-83a0-f0fc60bf4d1e
-- title:
--   Regularized $d$-th order Taylor model $f_x(y)$ (Eq. (2.4))
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be $d$ times differentiable, $M \in \mathbb R$, and $x \in \mathbb R^n$. The **regularized tensor approximation** of $f$ at $x$ is
--
--   $$f_x(y) := f(x) + \nabla f(x)^\top(y-x) + \frac12\nabla^2 f(x)[y-x]^2 + \cdots + \frac1{d!}\nabla^d f(x)[y-x]^d + \frac{M}{(d+1)!}\|y-x\|^{d+1},$$
--
--   the $d$-th order Taylor polynomial of $f$ at $x$ plus a regularization term of order $d+1$, where $\nabla^i f(x)[z]^i$ is the $i$-th derivative tensor evaluated at $(z,\dots,z)$ and $\|\cdot\|$ is the Euclidean norm. The paper uses it with $M>0$.
--
--   It is the model minimized (together with $h$ and a proximal term) in each iteration of the optimal tensor method, and its gradient enters the update (3.10).
--
--   **Formalization Note** $\nabla^i f(x)[z]^i$ is Mathlib's `iteratedFDeriv ℝ i f x` applied to the constant family $(z,\dots,z)$; the space is `EuclideanSpace ℝ (Fin n)`. The sign condition $M>0$ is a hypothesis of the statements, not part of the definition.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Eq. (2.4), p.5

import Mathlib

namespace TensorAHPE

/-- **The regularized d-th order Taylor model `f_x`.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Eq. (2.4), p.5:
"f_x(y) := f(x) + ∇f(x)ᵀ(y − x) + (1/2)∇²f(x)[y − x]² + ⋯ + (1/d!)∇ᵈf(x)[y − x]ᵈ
+ (M/(d + 1)!)‖y − x‖^{d+1}, where M > 0 is the parameter of the high-order regularization
term".

`model f d M x y` is `∑_{i=0}^{d} (1/i!) ∇ⁱf(x)[y − x]ⁱ + (M/(d+1)!) ‖y − x‖^{d+1}`.

**Formalization Note.** `∇ⁱf(x)[z]ⁱ` is Mathlib's `iteratedFDeriv ℝ i f x` applied to the
constant family `(z, …, z)`; the `i = 0` term is `f x` and the `i = 1` term is
`⟨∇f(x), z⟩`. The space is `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm. The
condition `M > 0` is a hypothesis of the statements that use the model, not part of this
definition. -/
noncomputable def model {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (d : ℕ) (M : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i ∈ Finset.range (d + 1),
      (1 / (i.factorial : ℝ)) * iteratedFDeriv ℝ i f x (fun _ => y - x)) +
    M / ((d + 1).factorial : ℝ) * ‖y - x‖ ^ (d + 1)

end TensorAHPE


