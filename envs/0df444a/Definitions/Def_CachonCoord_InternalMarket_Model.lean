-- Prove2me | Definitions.Def_CachonCoord_InternalMarket_Model
-- name    : CachonCoord_InternalMarket_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:10.505318+00:00
-- url     : https://prove2.me/theorems/9d5a5c74-aef5-48b6-a9d8-28b93e03b686
-- title:
--   §6.9.1, pp. 92–94 — the internal-market model: shocks A₁, A₂ > 0, Y ∈ [0, 1], cost c(e), profit Π(e), the payment (46) and the manager's utility u(e)
-- statement:
--   The stochastic model of §6.9.1 (after Kouvelis and Lariviere, 2000). One supplier, her production manager and two independent retailers. The manager chooses a production input level $e\ge0$, which yields $Q=Ye$ finished units, where $Y\in[0,1]$ is random, and incurs the cost $c(e)$, strictly convex and increasing on $[0,\infty)$ and differentiable on $(0,\infty)$ with derivative $c'$. Retailer $i$ observes the realization $\alpha_i$ of a random variable $A_i>0$. The demand elasticity is a constant $\eta>1$. The random variables $A_1,A_2,Y$ are measurable functions on a probability space $(\Omega,P)$.
--
--   On top of the realization-wise objects of the Revenue file, the file defines:
--
--   1. **Expected supply chain profit** $\Pi(e)=E[\pi(A,Ye)]-c(e)$, where $\pi(\alpha,Q)$ is the retailers' revenue under the allocation $\gamma^o(\alpha)$.
--   2. **The constant** $K=E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]$.
--   3. **The per-unit payment** to the manager for a target effort $e^o$, the left side of (46):
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}\,K\,/\,E[Y].
--   $$
--   4. **Expected output** $E[Q\mid e]=E[Ye]$ and the supplier's **expected market revenue** $E[Qw(A,Q)\mid e]$ with $Q=Ye$.
--   5. **The manager's expected utility** under that payment, $u(e)=(\text{payment per unit})\cdot E[Ye]-c(e)$.
--
--   These are the objects of (45), (46) and of the manager's incentive problem.
--
--   **Formalization Note** "Strictly convex and increasing" is stated on $[0,\infty)$, the range of efforts; differentiability is assumed only on $(0,\infty)$, as $u'$ and (45) use it there. Measurability of $A_1,A_2,Y$ is the standing convention for random variables. Integrability of the integrand of $K$ and $E[Y]>0$ are not part of the model; the theorems that need them assume them. When $Y=0$ the realized output is $Q=0$, where $w(\alpha,0)$ is undefined; Lean evaluates $Q\,w(A,Q)$ there as $0$, which is its limit as $Q\downarrow0$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 92 (model), p. 93 (Π(e, A, Y), Eq. (45)), p. 94 (Eq. (46), u(e))

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- The model of §6.9.1 (Cachon 2003, 3rd draft, p. 92), after Kouvelis and Lariviere (2000).
The production manager chooses an input level `e ≥ 0`, which yields the output `Q = Y e`, where
`Y ∈ [0, 1]` is random; he incurs the cost `c(e)`, strictly convex and increasing. Retailer `i`
observes the realization `αᵢ` of the random variable `Aᵢ > 0`. The constant demand elasticity is
`η > 1`. The random variables live on a probability space `(Ω, P)`; `c'` is the derivative of `c`
on `(0, ∞)`. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  /-- The constant demand elasticity `η`. -/
  η : ℝ
  /-- `η > 1`. -/
  one_lt_η : 1 < η
  /-- The probability measure. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- Retailer one's demand shock `A₁`. -/
  A₁ : Ω → ℝ
  /-- Retailer two's demand shock `A₂`. -/
  A₂ : Ω → ℝ
  /-- The output shock `Y`. -/
  Y : Ω → ℝ
  meas_A₁ : Measurable A₁
  meas_A₂ : Measurable A₂
  meas_Y : Measurable Y
  /-- `A₁ > 0`. -/
  A₁_pos : ∀ ω, 0 < A₁ ω
  /-- `A₂ > 0`. -/
  A₂_pos : ∀ ω, 0 < A₂ ω
  /-- `Y ∈ [0, 1]`. -/
  Y_mem : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1
  /-- The production manager's cost `c(e)`. -/
  c : ℝ → ℝ
  /-- The derivative `c'(e)` for `e > 0`. -/
  c' : ℝ → ℝ
  /-- `c` is strictly convex on `e ≥ 0`. -/
  c_strictConvex : StrictConvexOn ℝ (Set.Ici 0) c
  /-- `c` is increasing on `e ≥ 0`. -/
  c_mono : MonotoneOn c (Set.Ici 0)
  /-- `c` is differentiable at every `e > 0` with derivative `c'(e)`. -/
  c_hasDeriv : ∀ e : ℝ, 0 < e → HasDerivAt c (c' e) e

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

/-- Total expected supply chain profit `Π(e, A, Y) = E[π(A, Ye)] − c(e)` (§6.9.1, p. 93), where
`π(α, Q)` is the retailers' revenue under the optimal allocation. -/
noncomputable def chainProfit (e : ℝ) : ℝ :=
  (∫ ω, optRevenue M.η (M.A₁ ω) (M.A₂ ω) (M.Y ω * e) ∂M.P) - M.c e

/-- The constant `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` appearing in (45) and (46). -/
noncomputable def K : ℝ :=
  ∫ ω, (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) * M.Y ω ^ ((M.η - 1) / M.η) ∂M.P

/-- The per-unit payment to the production manager, the left side of (46) (§6.9.1, p. 94):
`((η − 1)/η) (e°)^{−1/η} E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}] / E[Y]`, for a target effort `e°`. -/
noncomputable def payRate (eo : ℝ) : ℝ :=
  ((M.η - 1) / M.η) * eo ^ (-1 / M.η) * M.K / ∫ ω, M.Y ω ∂M.P

/-- Expected output `E[Q | e] = E[Y e]`. -/
noncomputable def expOutput (e : ℝ) : ℝ :=
  ∫ ω, M.Y ω * e ∂M.P

/-- The supplier's expected revenue from the internal market at effort `e`,
`E[Q w(A, Q) | e]` with `Q = Y e`: each realized unit is sold at the market price `w(A, Q)`. -/
noncomputable def expMarketRevenue (e : ℝ) : ℝ :=
  ∫ ω, (M.Y ω * e) * price M.η (M.A₁ ω) (M.A₂ ω) (M.Y ω * e) ∂M.P

/-- The production manager's expected utility at effort `e` when the supplier pays him the rate
(46) set for the target effort `e°` per unit of realized output (§6.9.1, p. 94):
`u(e) = payRate(e°) · E[Y e] − c(e)`. -/
noncomputable def managerUtility (eo e : ℝ) : ℝ :=
  M.payRate eo * M.expOutput e - M.c e

end Model

end CachonCoord.InternalMarket


