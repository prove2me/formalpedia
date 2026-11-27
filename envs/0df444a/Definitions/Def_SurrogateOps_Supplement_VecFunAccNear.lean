-- Prove2me | Definitions.Def_SurrogateOps_Supplement_VecFunAccNear
-- name    : SurrogateOps_Supplement_VecFunAccNear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:36:21.806915+00:00
-- url     : https://prove2.me/theorems/ad85b8fe-8b9b-45c3-927e-9b1235ff8534
-- title:
--   Definition 1, p.3, for maps into $\mathbb R^m$ (§5, p.18) — order-$N$ function accuracy near $x_0$ of a vector-valued class of models
-- statement:
--   Let $E$ and $G$ be real normed spaces, $f:E\to G$, $x_0\in E$, $\bar\Delta>0$, $N\ge0$ and $\kappa\ge0$. The class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ of $f$ has order-$N$ function accuracy near $x_0$ with constant $\kappa$ if
--
--   $$
--   \|f(x)-\tilde f_\Delta(x)\|\le\kappa\,\Delta^N
--   $$
--
--   for all $\Delta\in(0,\bar\Delta]$ and all $x\in B_\Delta(x_0)$, where $\|\cdot\|$ is the norm of $G$ (on $\mathbb R^m$, the Euclidean norm). Here $B_\Delta(x_0)$ is the closed ball whose radius is the model's own index $\Delta$.
--
--   This is the paper's Definition 1 (and its gradient and Hessian analogues) for a vector-valued map. Section 5 applies it to the inner map $f_1:\mathbb R^d\to\mathbb R^m$ of a composition $F=f_2\circ f_1$; the published real-valued predicate `SurrogateOps.FunAccNear` covers the outer function $f_2$.
--
--   **Formalization Note** The class of models is a map `fm : ℝ → E → G` of which only the values at $\Delta\in(0,\bar\Delta]$ are used, and $\Delta^N$ is the real power. The constant $\kappa$ is an argument of the predicate, so "provides order-$N$ accuracy" is `∃ κ, …`.
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Definition 1, p.3; §5, p.18

import Mathlib

namespace SurrogateOps.Supplement

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Order-`N` function accuracy near `x0` with constant `κ`, for a class of models of a map
`f : E → G` with values in a normed space (in §5, the inner map `f₁ : ℝ^d → ℝ^m`). The bound holds on the closed ball
`B_Δ(x0)` whose radius is the model's own index `Δ`.
Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Definition 1, p.3; used for `f₁ : ℝ^d → ℝ^m` in §5, p.18.

**Formalization Note.** The vector-valued analogue of `SurrogateOps.FunAccNear`, which is stated for
real-valued functions only. A class of models `{f̃_Δ}_{(0,Δ̄]}` is a map `fm : ℝ → E → G` of which only
the values at `Δ ∈ Set.Ioc 0 Δbar` are used. `Δ ^ N` is `Real.rpow`, `Δ > 0`. The constant `κ` is an
argument, so "provides order-`N` accuracy" is `∃ κ, …`; the page's `N ≥ 0` and `κ ≥ 0` are clauses.
The paper's `‖·‖` is the norm of `G` (on `ℝ^m`, the Euclidean norm). -/
def VecFunAccNear (f : E → G) (fm : ℝ → E → G) (x0 : E) (Δbar N κ : ℝ) : Prop :=
  0 ≤ N ∧ 0 ≤ κ ∧ ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ‖f x - fm Δ x‖ ≤ κ * Δ ^ N

end SurrogateOps.Supplement


