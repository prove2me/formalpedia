-- Prove2me | Definitions.Def_RiemSmoothSD_IsSmoothingFunction
-- name    : RiemSmoothSD_IsSmoothingFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:26.844988+00:00
-- url     : https://prove2.me/theorems/8c48fdec-02ee-431a-b776-51f339f375a0
-- title:
--   Smoothing function $\tilde f$ of $f$ (Definition 2.7)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $f:E\to\mathbb R$. A function $\tilde f:E\times\mathbb R_+\to\mathbb R$ is a **smoothing function** of $f$ if
--
--   1. $\tilde f(\cdot,\mu)$ is continuously differentiable on $E$ for every $\mu>0$;
--   2. for every $x\in E$,
--   $$
--   \lim_{z\to x,\ \mu\downarrow0}\tilde f(z,\mu)=f(x);
--   $$
--   3. there are a constant $\kappa>0$ and a function $\omega:\mathbb R_{++}\to\mathbb R_{++}$ with $\lim_{\mu\downarrow0}\omega(\mu)=0$ such that
--   $$
--   |\tilde f(x,\mu)-f(x)|\le\kappa\,\omega(\mu)\qquad\text{for all }x\in E,\ \mu>0.
--   $$
--
--   Smoothing functions replace a nonsmooth, possibly non-Lipschitz objective by a family of $C^1$ approximations; the RSSD method runs Riemannian gradient steps on $\tilde f(\cdot,\mu)$ while driving $\mu$ to $0$.
--
--   **Formalization Note** $\tilde f$ is a function `E → ℝ → ℝ`; its values at $\mu\le0$, and those of $\omega$, are unconstrained and never used. "$\mu\downarrow0$" is the right neighbourhood filter of $0$.
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Definition 2.7, (2.2)–(2.3), p.5

import Mathlib
set_option autoImplicit false
open Filter Topology

namespace RiemSmoothSD

/-- **Smoothing function** (Zhang, Chen & Ma, *A Riemannian Smoothing Steepest Descent Method for
Non-Lipschitz Optimization on Submanifolds*, arXiv:2104.04199v1, Definition 2.7, p.5).
A function `f̃ : ℝⁿ × ℝ₊ → ℝ` is a smoothing function of `f : ℝⁿ → ℝ` if
`f̃(·, μ)` is continuously differentiable on `ℝⁿ` for every `μ > 0`,
`lim_{z → x, μ ↓ 0} f̃(z, μ) = f(x)` (2.2), and there are `κ > 0` and `ω : ℝ₊₊ → ℝ₊₊` with
`|f̃(x, μ) − f(x)| ≤ κ ω(μ)` and `lim_{μ ↓ 0} ω(μ) = 0` (2.3).

**Formalization Note** The ambient space `ℝⁿ` is a finite-dimensional real inner product space
`E` (ℝⁿ and matrix spaces with the trace inner product are instances). `f̃` is a function
`E → ℝ → ℝ`, `ftilde z μ = f̃(z, μ)`; its values at `μ ≤ 0` are unconstrained and never used.
"`μ ↓ 0`" is the right neighbourhood filter `𝓝[>] 0`. `ω` is a function `ℝ → ℝ` that is positive
on `(0, ∞)`; its values at `μ ≤ 0` are unconstrained. -/
def IsSmoothingFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (ftilde : E → ℝ → ℝ) : Prop :=
  (∀ μ : ℝ, 0 < μ → ContDiff ℝ 1 (fun z => ftilde z μ)) ∧
  (∀ x : E, Tendsto (fun p : E × ℝ => ftilde p.1 p.2) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (f x))) ∧
  ∃ κ : ℝ, 0 < κ ∧ ∃ ω : ℝ → ℝ, (∀ μ : ℝ, 0 < μ → 0 < ω μ) ∧
    Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    ∀ x : E, ∀ μ : ℝ, 0 < μ → |ftilde x μ - f x| ≤ κ * ω μ

end RiemSmoothSD


