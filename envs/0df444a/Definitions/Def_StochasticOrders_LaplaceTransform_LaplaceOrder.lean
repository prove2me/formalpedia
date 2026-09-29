-- Prove2me | Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
-- name    : StochasticOrders_LaplaceTransform_LaplaceOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:28.018984+00:00
-- url     : https://prove2.me/theorems/5728adaf-ab8f-4973-bc7c-b9d8bf24767e
-- title:
--   The Laplace transform order
-- statement:
--   Let $X$ be a real-valued random variable on a probability space $(\Omega,\mu)$ and let $Y$ be
--   a real-valued random variable on a (possibly different) probability space $(\Omega',\nu)$. $X$
--   is said to be **smaller than $Y$ in the Laplace transform order**, written $X \le_{Lt} Y$, if
--
--   $$E[e^{-sX}] \ge E[e^{-sY}] \quad \text{for all } s > 0.$$
--
--   The Laplace transform order corresponds to comparing $E[\varphi(X)]$ against $E[\varphi(Y)]$
--   for the single function $\varphi(x) = -e^{-sx}$, $s > 0$ — the same scheme that produces the
--   usual stochastic order (all increasing $\varphi$) and the convex order (all convex $\varphi$).
--   It is meant for nonnegative random variables, the chapter's standing convention: the transform
--   $E[e^{-sX}]$ need not even be finite otherwise. This order compares both the "location" and
--   the "spread" of $X$ and $Y$.
--
--   **Formalization Note** `LaplaceOrder μ ν X Y` quantifies over every real `s > 0` and compares
--   the two measures' expectations of `exp(-sX)`/`exp(-sY)` directly — `X` and `Y` need not share a
--   probability space, and nonnegativity of `X`, `Y` is carried as an explicit hypothesis on every
--   theorem that needs it rather than built into the order itself, matching the series' earlier
--   definitions (e.g. `StochasticOrders.Usual.UsualOrder`).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 233, Eq. (5.A.1)

import Mathlib

namespace StochasticOrders.LaplaceTransform

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The Laplace transform order `X ≤Lt Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 233, Eq. (5.A.1)): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y`
on a (possibly different) probability space `(Ω', ν)` in the Laplace transform order if
`E[exp{-sX}] ≥ E[exp{-sY}]` for every `s > 0`. The order is meant for nonnegative random variables
(§5.A.1's standing convention); that hypothesis is carried explicitly on each theorem that uses it,
not built into this definition. -/
def LaplaceOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∫ ω, Real.exp (-(s * X ω)) ∂μ ≥ ∫ ω, Real.exp (-(s * Y ω)) ∂ν

end StochasticOrders.LaplaceTransform


