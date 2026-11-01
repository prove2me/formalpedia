-- Prove2me | Definitions.Def_ExpConMinimax_Assumption21
-- name    : ExpConMinimax_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:28.596978+00:00
-- url     : https://prove2.me/theorems/46f35868-9c70-442c-a34e-e72ab24afb0a
-- title:
--   Assumption 2.1 — Lipschitz objective, unbiased sampled subgradients with second moments $\le C_f^2$
-- statement:
--   Let $C_f>0$. **Assumption 2.1** requires:
--
--   1. for every $x\in\mathcal X$, $|F(x,y_1)-F(x,y_2)|\le C_f\|y_1-y_2\|$ for all $y_1,y_2\in\mathcal Y$, and for every $y\in\mathcal Y$, $|F(x_1,y)-F(x_2,y)|\le C_f\|x_1-x_2\|$ for all $x_1,x_2\in\mathcal X$;
--   2. for every $x\in\mathcal X$, $y\in\mathcal Y$, the sampled subgradients are unbiased,
--   $$\mathbb E[\widetilde\nabla_xf(x,y,\omega)]=\widetilde\nabla_xF(x,y)\in\partial_xF(x,y),\qquad \mathbb E[\widetilde\nabla_yf(x,y,\omega)]=\widetilde\nabla_yF(x,y)\in\partial_yF(x,y),$$
--   and have bounded second moments $\mathbb E\|\widetilde\nabla_xf(x,y,\omega)\|^2\le C_f^2$, $\mathbb E\|\widetilde\nabla_yf(x,y,\omega)\|^2\le C_f^2$.
--
--   **Formalization Note** $P_\omega$ is a probability measure. $\partial_xF$ is read as the subgradient inequality of $F(\cdot,y)$ relative to $\mathcal X$ and $\partial_yF$ as the supergradient inequality of the concave $F(x,\cdot)$ relative to $\mathcal Y$. Finite second moments are stated as square integrability.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Assumption 2.1, p.9

import Mathlib
import Definitions.Def_ExpConMinimax_Problem
import Definitions.Def_ExpConMinimax_Oracle
import Definitions.Def_ExpConMinimax_IsSubgradOn

namespace ExpConMinimax

open MeasureTheory

/-- **Assumption 2.1** (objective).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Assumption 2.1, p.9:

"Let `C_f` be a positive scalar. The function `f` satisfies
1. For every `x ∈ X`, the function `F(x,·)` is Lipschitz continuous, i.e.,
   `‖F(x,y₁) − F(x,y₂)‖ ≤ C_f‖y₁ − y₂‖, ∀y₁,y₂ ∈ Y`.
   For every `y ∈ Y`, the function `F(·,y)` is Lipschitz continuous, i.e.,
   `‖F(x₁,y) − F(x₂,y)‖ ≤ C_f‖x₁ − x₂‖, ∀x₁,x₂ ∈ X`.
2. For every `x ∈ X` and `y ∈ Y`, the sampled sub-gradients `∇̃ₓf(x,y,ω)` and `∇̃_yf(x,y,ω)` are
   unbiased such that `E[∇̃ₓf(x,y,ω)] = ∇̃ₓF(x,y) ∈ ∂ₓF(x,y)`, and
   `E[∇̃_yf(x,y,ω)] = ∇̃_yF(x,y) ∈ ∂_yF(x,y)` and preserve bounded second moments such that
   `E[‖∇̃ₓf(x,y,ω)‖²] ≤ C_f²`, and `E[‖∇̃_yf(x,y,ω)‖²] ≤ C_f²`."

**Formalization Note.** `μω` is a probability measure (the law of `ω`). The means `∇̃ₓF(x,y)`,
`∇̃_yF(x,y)` are `Oracle.meanGfx`, `Oracle.meanGfy`. "`∈ ∂ₓF(x,y)`" is the subgradient
inequality of the convex function `F(·,y)` relative to `X` (`IsSubgradOn`); "`∈ ∂_yF(x,y)`" is
the supergradient inequality of the concave function `F(x,·)` relative to `Y`
(`IsSupergradOn`). The finite second moments are encoded as `MemLp · 2`, which also records
the measurability that `E[·]` presupposes. -/
def Assumption21 {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] (P : Problem dx dy m₁ m₂)
    (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (Cf : ℝ) : Prop :=
  0 < Cf ∧ IsProbabilityMeasure O.μω ∧
  (∀ x ∈ P.X, ∀ y₁ ∈ P.Y, ∀ y₂ ∈ P.Y, |P.F x y₁ - P.F x y₂| ≤ Cf * ‖y₁ - y₂‖) ∧
  (∀ y ∈ P.Y, ∀ x₁ ∈ P.X, ∀ x₂ ∈ P.X, |P.F x₁ y - P.F x₂ y| ≤ Cf * ‖x₁ - x₂‖) ∧
  ∀ x ∈ P.X, ∀ y ∈ P.Y,
    MemLp (O.gfx x y) 2 O.μω ∧
    IsSubgradOn (fun x' => P.F x' y) P.X x (O.meanGfx x y) ∧
    ∫ s, ‖O.gfx x y s‖ ^ 2 ∂O.μω ≤ Cf ^ 2 ∧
    MemLp (O.gfy x y) 2 O.μω ∧
    IsSupergradOn (fun y' => P.F x y') P.Y y (O.meanGfy x y) ∧
    ∫ s, ‖O.gfy x y s‖ ^ 2 ∂O.μω ≤ Cf ^ 2

end ExpConMinimax


