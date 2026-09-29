-- Prove2me | Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
-- name    : StochasticOrders_MeanResidualLife_MrlOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:42.777262+00:00
-- url     : https://prove2.me/theorems/8a8fe08d-4136-4477-81e5-2a6cc7af850a
-- title:
--   The mean residual life order
-- statement:
--   Let $X$ on $(\Omega,\mu)$ have mrl function $m$ and let $Y$ on a (possibly different)
--   probability space $(\Omega',\nu)$ have mrl function $l$. $X$ is said to be **smaller than $Y$
--   in the mean residual life order**, written $X \le_{mrl} Y$, if
--
--   $$m(t) \le l(t) \quad \text{for all } t.$$
--
--   Intuitively: the smaller the mrl function, the smaller $X$ should be in a stochastic sense.
--   Unlike the usual stochastic order, $\le_{mrl}$ compares a *derived* function of $X$ and $Y$
--   pointwise, not a function-class family of expectations, and neither order implies the other
--   in general.
--
--   **Formalization Note** `MrlOrder μ ν X Y := ∀ t : ℝ, mrl μ X t ≤ mrl ν Y t` — the comparison
--   is over every real `t` (not restricted to a common support), matching the book's own "for all
--   $t$", since `mrl` already encodes the "$0$ outside the support" convention uniformly.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 82, Eq. (2.A.2)

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The mean residual life order `X ≤mrl Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 82, Eq. (2.A.2)): a random variable `X` on `(Ω, μ)` with mrl function `m` is smaller than
a random variable `Y` on a (possibly different) probability space `(Ω', ν)` with mrl function `l`
in the mean residual life order if `m(t) ≤ l(t)` for every real `t`. -/
def MrlOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ t : ℝ, mrl μ X t ≤ mrl ν Y t

end StochasticOrders.MeanResidualLife


