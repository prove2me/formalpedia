-- Prove2me | Definitions.Def_InfHorizonVP_HypH8
-- name    : InfHorizonVP_HypH8
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:23.906671+00:00
-- url     : https://prove2.me/theorems/b16c3967-169c-42b4-97e8-82d6b9cff5d2
-- title:
--   Hypothesis (H8): interiority along $x_0$
-- statement:
--   **(H8)** For every $T>0$ there exists $\eta>0$ such that for almost every $t\in[0,T]$,
--   $$
--   \dot x_0(t)\in\Gamma(t,x_0(t)+\eta v)\quad\text{for every } v\in B,
--   $$
--   i.e. $(x_0(t)+\eta B,\dot x_0(t))\subset\operatorname{gph}\Gamma(t,\cdot)$, where $B$ is the open unit ball.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §4.1, pp.11–12, (H8)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H8): interiority along `x₀`.**
Frankowska, Sagara, arXiv:1801.00400v3, §4.1, pp.11–12: "(H8) For every T > 0 there exists η > 0
such that (x0(t) + ηB, ẋ0(t)) ⊂ gph Γ(t, ·) a.e. t ∈ [0, T]. This is equivalent to saying that
for every T > 0 there exists η > 0 such that a.e. t ∈ [0, T] we have ẋ0(t) ∈ Γ(t, x0(t) + ηv) for
every v ∈ B."

**Formalization Note.** The second (equivalent) form on the page is used; `B` is the open unit
ball and `ẋ₀(t)` is `deriv x₀ t`. -/
def HypH8 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : ℝ → E → Set E) (x₀ : ℝ → E) : Prop :=
  ∀ T, 0 < T → ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
    ∀ v ∈ Metric.ball (0 : E) 1, deriv x₀ t ∈ Γ t (x₀ t + η • v)

end InfHorizonVP


