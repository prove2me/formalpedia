-- Prove2me | Definitions.Def_SurrogateOps_Supplement_VecHessAccAt
-- name    : SurrogateOps_Supplement_VecHessAccAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:37:10.565257+00:00
-- url     : https://prove2.me/theorems/ad8c220e-59b7-5b50-99b1-3ecac9daa6ae
-- title:
--   Definition 1, p.3, for maps into $\mathbb R^m$ (§5, p.18) — order-$N$ Hessian accuracy at $x_0$ of a vector-valued class of models
-- statement:
--   Let $E$ and $G$ be real normed spaces, $f:E\to G$, $x_0\in E$, $\bar\Delta>0$, $N\ge0$ and $\kappa\ge0$. The class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ of $f$ has order-$N$ Hessian accuracy at $x_0$ with constant $\kappa$ if
--
--   $$
--   \|\nabla^2 f(x_0)-\nabla^2\tilde f_\Delta(x_0)\|\le\kappa\,\Delta^N
--   $$
--
--   for all $\Delta\in(0,\bar\Delta]$, where $\|\cdot\|$ is the operator norm of the second derivative $\nabla^2f(x)=D^2f(x)$, a bilinear map $E\times E\to G$.
--
--   This is the paper's Definition 1 (and its gradient and Hessian analogues) for a vector-valued map. Section 5 applies it to the inner map $f_1:\mathbb R^d\to\mathbb R^m$ of a composition $F=f_2\circ f_1$; the published real-valued predicate `SurrogateOps.HessAccAt` covers the outer function $f_2$.
--
--   **Formalization Note** The class of models is a map `fm : ℝ → E → G` of which only the values at $\Delta\in(0,\bar\Delta]$ are used, and $\Delta^N$ is the real power. The constant $\kappa$ is an argument of the predicate, so "provides order-$N$ accuracy" is `∃ κ, …`.
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Definition 1 and the paragraph after Example 2, p.3; §5, p.18

import Mathlib

namespace SurrogateOps.Supplement

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Order-`N` Hessian accuracy at `x0` with constant `κ`, for a class of models of a map
`f : E → G` with values in a normed space (in §5, the inner map `f₁ : ℝ^d → ℝ^m`).
Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Definition 1 and the paragraph after Example 2, p.3 (replace `f(·)` by `∇²f(·)`); used for `f₁ : ℝ^d → ℝ^m` in §5, p.18.

**Formalization Note.** The vector-valued analogue of `SurrogateOps.HessAccAt`, which is stated for
real-valued functions only. A class of models `{f̃_Δ}_{(0,Δ̄]}` is a map `fm : ℝ → E → G` of which only
the values at `Δ ∈ Set.Ioc 0 Δbar` are used. `Δ ^ N` is `Real.rpow`, `Δ > 0`. The constant `κ` is an
argument, so "provides order-`N` accuracy" is `∃ κ, …`; the page's `N ≥ 0` and `κ ≥ 0` are clauses.
The second derivative is `fderiv ℝ (fderiv ℝ f) x : E →L[ℝ] E →L[ℝ] G`, with its operator norm.
`fderiv` is `0` where a function is not differentiable, so the theorems state the twice
differentiability of the models. -/
def VecHessAccAt (f : E → G) (fm : ℝ → E → G) (x0 : E) (Δbar N κ : ℝ) : Prop :=
  0 ≤ N ∧ 0 ≤ κ ∧ ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fderiv ℝ f) x0 - fderiv ℝ (fderiv ℝ (fm Δ)) x0‖ ≤ κ * Δ ^ N

end SurrogateOps.Supplement


