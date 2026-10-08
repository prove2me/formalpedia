-- Prove2me | Definitions.Def_WhitinPrice_StyleGoods_Model
-- name    : WhitinPrice_StyleGoods_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:20.369772+00:00
-- url     : https://prove2.me/theorems/0c263eb3-7fb1-4ad9-b2b6-f66d4450715e
-- title:
--   Section 3, pp. 64–66 — the style-goods model with demand depending on unit profit: mean demand, uniform demand law, f, g, the expected profit (10) and x_M (12)
-- statement:
--   This file sets up the single-period **style-goods model** of Whitin (1955, §3) in which the demand distribution depends on the unit profit. Stock is on hand at the start of the period; units left at its close are liquidated at a loss.
--
--   The data are three real numbers: $P_0$, the unit profit at which demand falls to zero; $L$, the unit liquidation loss; and $k$, the reciprocal of the slope of the line relating unit profit and amount demanded. The decision variables are the unit profit $P$ and the stock $x$.
--
--   1. **Mean demand** is the linear function of $P$ that vanishes at $P = P_0$ and has slope $1/k$ in the (demand, unit-profit) plane:
--   $$\mu(P) = k\,(P - P_0).$$
--   It is positive for $0 < P < P_0$ exactly when $k < 0$.
--   2. **Demand** $X$ at unit profit $P$ has the rectangular (uniform) distribution on the interval from $0$ to twice mean demand, $X \sim \mathrm{Uniform}[0, 2\mu(P)]$.
--   3. The **expected marginal profit** and **expected marginal loss** of the $x$-th unit are
--   $$f(x) = P\,\Pr(X \ge x), \qquad g(x) = L\,\Pr(X < x):$$
--   the probability of selling the marginal unit weighted by the unit profit, and the probability of not selling it weighted by the liquidation loss.
--   4. The **expected profit** of stocking $x$ units at unit profit $P$ is the area between the two curves,
--   $$E(P, x) = \int_0^x \big[f(t) - g(t)\big]\,dt,$$
--   which equals $P\,\mathbb E[\min(X, x)] - L\,\mathbb E[(x - X)^+]$, the expected profit on sales minus the expected liquidation loss.
--   5. The **equilibrium stock** of Eq. (12) is
--   $$x_M(P) = -\frac{2kP(P_0 - P)}{P + L}.$$
--
--   Every statement of the mission is about these objects: the closed forms (11), (13), (14) and the optimal unit profit (16) are theorems about them, not definitions.
--
--   **Formalization Note** The uniform law is Lebesgue measure conditioned on $[0, 2\mu(P)]$ (`ProbabilityTheory.cond volume (Set.Icc 0 (2 * meanDemand k P₀ P))`); when $2\mu(P) \le 0$ the interval is null and this is the zero measure, so every theorem assumes $k < 0$ and $0 < P < P_0$. Probabilities are `Measure.real` of the sets $[x, \infty)$ and $(-\infty, x)$; for a continuous law the choice of $\ge$ versus $>$ is immaterial. $E(P, x)$ is defined for every real $x$ by an interval integral (the integrand is bounded and monotone, so it is integrable on bounded intervals); the theorems use it for $x \ge 0$. The paper's goodwill loss $G$ of Eq. (8) does not appear in this price-dependent model.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), pp. 63–66, Section 3 (p. 63 setup; p. 64 definition of f and g; p. 66 Eqs. (10)–(12) and the rectangular-demand illustration)

import Mathlib

namespace WhitinPrice.StyleGoods

open MeasureTheory ProbabilityTheory

/-- Mean demand at unit profit `P` (Whitin 1955, §3, p. 66): the line relating unit profit and
amount demanded, with reciprocal slope `k` and zero demand at `P = P₀`, i.e. `μ(P) = k (P − P₀)`.
It is positive for `P < P₀` exactly when `k < 0`. -/
noncomputable def meanDemand (k P₀ P : ℝ) : ℝ := k * (P - P₀)

/-- The demand law at unit profit `P` (§3, p. 66): the rectangular (uniform) distribution on the
interval from `0` to twice mean demand, `[0, 2 μ(P)]`, i.e. Lebesgue measure conditioned on that
interval. (When `2 μ(P) ≤ 0` the interval is null and this is the zero measure; every theorem
assumes `k < 0` and `P < P₀`.) -/
noncomputable def demandLaw (k P₀ P : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc 0 (2 * meanDemand k P₀ P))

/-- `f(x)` (§3, p. 64): the probability of selling the marginal (`x`-th) unit, i.e. that demand
is at least `x`, weighted by the unit profit `P`. -/
noncomputable def marginalProfit (k P₀ P x : ℝ) : ℝ :=
  P * (demandLaw k P₀ P).real (Set.Ici x)

/-- `g(x)` (§3, p. 64): the probability of not selling the marginal (`x`-th) unit, i.e. that
demand is less than `x`, weighted by the unit liquidation loss `L`. -/
noncomputable def marginalLoss (k P₀ L P x : ℝ) : ℝ :=
  L * (demandLaw k P₀ P).real (Set.Iio x)

/-- Expected profit `E(P, x)` of stocking `x` units at unit profit `P` (§3, Eq. (10), p. 66):
`∫₀ˣ [f(t) − g(t)] dt`, the expected profit on sales minus the expected liquidation loss. -/
noncomputable def expectedProfit (k P₀ L P x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (marginalProfit k P₀ P t - marginalLoss k P₀ L P t)

/-- The equilibrium stock `x_M(P, L) = −2kP(P₀ − P)/(P + L)` of Eq. (12), p. 66. -/
noncomputable def optimalStock (k P₀ L P : ℝ) : ℝ :=
  -(2 * k * P * (P₀ - P)) / (P + L)

end WhitinPrice.StyleGoods


