-- Prove2me | Definitions.Def_SurrogateOps_HessAccNear
-- name    : SurrogateOps_HessAccNear
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:12.223706+00:00
-- url     : https://prove2.me/theorems/aeb0a084-fb64-43e0-a92d-229dfb4739ea
-- title:
--   Definition 1 and p.3 — order-$N$ Hessian accuracy near $x_0$ with constant $\kappa$
-- statement:
--   Let $f:E\to\mathbb R$, let $x_0\in E$, $\bar\Delta>0$, $N\ge0$ and $\kappa\ge0$. The class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ of $f$ has order-$N$ Hessian accuracy near $x_0$ with constant $\kappa$ if
--
--   $$
--   \|\nabla^2 f(x)-\nabla^2 \tilde f_\Delta(x)\|\le\kappa\,\Delta^N
--   $$
--
--   for all $\Delta\in(0,\bar\Delta]$ and all $x\in B_\Delta(x_0)$. Here $B_\Delta(x_0)$ is the closed ball of radius $\Delta$, the model's own index, so the region shrinks with the model.
--
--   The class provides order-$N$ Hessian accuracy if some such $\kappa$ exists. A fully quadratic class of models provides order-1 Hessian accuracy.
--
--   **Formalization Note** The class of models is a map `fm : ℝ → E → ℝ` of which only the values at $\Delta\in(0,\bar\Delta]$ are used, and $\Delta^N$ is the real power. The constant $\kappa$ is an argument of the predicate, so "provides order-$N$ accuracy" is `∃ κ, …`. The space $E$ is any real normed space; the theorems of this mission use $E=\mathbb R^d$. The Hessian is `fderiv ℝ (fderiv ℝ f)` with the operator norm, which on $\mathbb R^d$ is the spectral norm of $\nabla^2f$.
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Definition 1 and the paragraph after Example 2, p.3

import Mathlib

namespace SurrogateOps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Order-`N` Hessian accuracy near `x0` with constant `κ`.
Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Definition 1, p.3, and the paragraph
after Example 2, p.3 (replace `f(·)` by `∇²f(·)`).

**Formalization Note.** A class of models `{f̃_Δ}_{(0,Δ̄]}` is a map `fm : ℝ → E → ℝ` of which only
the values at `Δ ∈ Set.Ioc 0 Δbar` are used. `Δ ^ N` is `Real.rpow`, `Δ > 0`. The constant `κ` is an
argument, so "provides order-`N` accuracy" is `∃ κ, …`; the page's `N ≥ 0` and `κ ≥ 0` are clauses.
The Hessian is `fderiv ℝ (fderiv ℝ f)`, with the operator norm of `E →L[ℝ] E →L[ℝ] ℝ` (on `ℝ^d` this
is the spectral norm of `∇²f`). `fderiv` is `0` where a function is not differentiable, so the
theorems state the twice differentiability of the models. -/
def HessAccNear (f : E → ℝ) (fm : ℝ → E → ℝ) (x0 : E) (Δbar N κ : ℝ) : Prop :=
  0 ≤ N ∧ 0 ≤ κ ∧ ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ (fm Δ)) x‖ ≤ κ * Δ ^ N

end SurrogateOps


