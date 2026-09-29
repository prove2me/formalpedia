-- Prove2me | Definitions.Def_StochasticOrders_MeanResidualLife_mrl
-- name    : StochasticOrders_MeanResidualLife_mrl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:22:25.750985+00:00
-- url     : https://prove2.me/theorems/7edd552b-82a7-42cf-9b95-55c7d581b855
-- title:
--   The mean residual life function
-- statement:
--   Let $X$ be a random variable on a probability space $(\Omega,\mu)$ with survival function
--   $\bar F$ and finite mean. The **mean residual life function** of $X$ at $t$ is
--
--   $$m(t) = \begin{cases} E[X-t \mid X>t], & t < t^*; \\ 0, & \text{otherwise}, \end{cases}$$
--
--   where $t^* = \sup\{t : \bar F(t) > 0\}$. When $X$ is nonnegative, $m(t)$ is the conditional
--   expected residual lifetime of a device still alive at time $t$. This function is the object
--   every order in this chapter is built from.
--
--   **Formalization Note** The case condition "$t < t^*$" is formalized directly as
--   `0 < (μ {ω | t < X ω}).toReal` (i.e. $\bar F(t) > 0$), its defining equivalent under the
--   survival function's monotonicity, rather than through the derived quantity $t^*$ itself.
--   "$E[X-t\mid X>t]$" is the standard conditional-expectation formula
--   `(∫ ω in {ω | t < X ω}, (X ω - t) ∂μ) / (μ {ω | t < X ω}).toReal`.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 81, Eq. (2.A.1)

import Mathlib

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mean residual life function `m(t)` of a random variable `X` on `(Ω, μ)` (Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 81, Eq. (2.A.1)): `m(t) = E[X - t | X > t]`
for `t < t*`, and `m(t) = 0` otherwise, where `t* = sup{t : P{X>t} > 0}`. The case condition
`t < t*` is formalized directly as `0 < P{X>t}`, its defining equivalent under the monotonicity of
the survival function `t ↦ P{X>t}`, rather than through the derived quantity `t*` itself. -/
noncomputable def mrl (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  if 0 < (μ {ω | t < X ω}).toReal then
    (∫ ω in {ω | t < X ω}, (X ω - t) ∂μ) / (μ {ω | t < X ω}).toReal
  else 0

end StochasticOrders.MeanResidualLife


