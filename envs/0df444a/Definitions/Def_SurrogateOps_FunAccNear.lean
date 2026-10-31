-- Prove2me | Definitions.Def_SurrogateOps_FunAccNear
-- name    : SurrogateOps_FunAccNear
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:59.907471+00:00
-- url     : https://prove2.me/theorems/82a5df44-dfe4-43f2-88ba-587bc54f8473
-- title:
--   Definition 1, p.3 — order-$N$ function accuracy near $x_0$ with constant $\kappa$
-- statement:
--   Let $f:E\to\mathbb R$, let $x_0\in E$, $\bar\Delta>0$, $N\ge0$ and $\kappa\ge0$. The class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ of $f$ has order-$N$ function accuracy near $x_0$ with constant $\kappa$ if
--
--   $$
--   |f(x)-\tilde f_\Delta(x)|\le\kappa\,\Delta^N
--   $$
--
--   for all $\Delta\in(0,\bar\Delta]$ and all $x\in B_\Delta(x_0)$. Here $B_\Delta(x_0)$ is the closed ball of radius $\Delta$, the model's own index, so the region shrinks with the model.
--
--   The class provides order-$N$ function accuracy if some such $\kappa$ exists. This is the paper's basic measure of model quality: a fully linear class provides order-2 function accuracy.
--
--   **Formalization Note** The class of models is a map `fm : ℝ → E → ℝ` of which only the values at $\Delta\in(0,\bar\Delta]$ are used, and $\Delta^N$ is the real power. The constant $\kappa$ is an argument of the predicate, so "provides order-$N$ accuracy" is `∃ κ, …`. The space $E$ is any real normed space; the theorems of this mission use $E=\mathbb R^d$.
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Definition 1, p.3

import Mathlib

namespace SurrogateOps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Order-`N` function accuracy near `x0` with constant `κ`: the bound holds on the closed ball
`B_Δ(x0)` whose radius is the model's own index `Δ`.
Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Definition 1, p.3.

**Formalization Note.** A class of models `{f̃_Δ}_{(0,Δ̄]}` is a map `fm : ℝ → E → ℝ` of which only
the values at `Δ ∈ Set.Ioc 0 Δbar` are used. `Δ ^ N` is `Real.rpow`, `Δ > 0`. The constant `κ` is an
argument, so "provides order-`N` accuracy" is `∃ κ, …`; the page's `N ≥ 0` and `κ ≥ 0` are clauses. -/
def FunAccNear (f : E → ℝ) (fm : ℝ → E → ℝ) (x0 : E) (Δbar N κ : ℝ) : Prop :=
  0 ≤ N ∧ 0 ≤ κ ∧ ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |f x - fm Δ x| ≤ κ * Δ ^ N

end SurrogateOps


