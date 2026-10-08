-- Prove2me | Definitions.Def_CachonCoord_MarketClearing_Contracts
-- name    : CachonCoord_MarketClearing_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:41.341783+00:00
-- url     : https://prove2.me/theorems/844da181-a78f-4d79-9d9c-af5b1ffbc31f
-- title:
--   §6.5.2, pp. 56–57 — resale price maintenance with proportional allocation, and the buy-back contract with the market price floored at b
-- statement:
--   Two contracts of §6.5.2, in the model of the Model file (prices $p_l(q)=(1-q)^+$, $p_h(q)=(1-q/\theta)^+$, states equally likely, zero salvage value and production cost).
--
--   1. **Resale price maintenance** $(\bar p,w)$: the retailers may not sell below $\bar p$. With total stock $Q$, in each state, if the market clearing price is at least $\bar p$ all stock is sold at that price; otherwise only the demand at price $\bar p$ is sold ($1-\bar p$ units in the low state, $\theta(1-\bar p)$ in the high state), at $\bar p$, and it is allocated in proportion to each retailer's stock. The expected revenue per unit of stock is
--   $$
--   \tfrac12\begin{cases}p_l(Q)&\bar p\le p_l(Q)\\ \bar p(1-\bar p)/Q&\text{otherwise}\end{cases}
--   +\tfrac12\begin{cases}p_h(Q)&\bar p\le p_h(Q)\\ \bar p\,\theta(1-\bar p)/Q&\text{otherwise,}\end{cases}
--   $$
--   and a retailer with $y=q(t)$ units earns $y$ times this minus $wy$.
--   2. **Buy-back** $(w,b)$: the supplier pays $b$ for every unsold unit, so the market price cannot fall below $b$: with total order $q$ the retailers sell $s_l=\min(q,1-b)$ units in the low state and $s_h=\min(q,\theta(1-b))$ in the high state. Their expected profit and the supplier's are
--   $$
--   \tfrac12\big(p_l(s_l)s_l+b(q-s_l)\big)+\tfrac12\big(p_h(s_h)s_h+b(q-s_h)\big)-wq,\qquad
--   wq-\tfrac12b(q-s_l)-\tfrac12b(q-s_h).
--   $$
--
--   These are the two mechanisms the section shows to restore the integrated profit.
--
--   **Formalization Note** The sales rules encode the page's equilibrium reasoning ("the market price cannot fall below 1/2 … the retailers sell at most 1/2 in the low demand state and θ/2 in the high demand state", p. 57; "proportional allocation", p. 56) as definitions; they are meant for $0\le\bar p\le1$ and $0\le b\le1$, and the theorems use only $\bar p=b=1/2$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, pp. 56–57

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- Resale price maintenance with floor price `p̄` (§6.5.2, pp. 56–57): expected revenue per
unit of stock when the retailers' total stock is `Q`. In each state, if the market clearing price
is at least `p̄` all stock sells at that price; otherwise only the demand at `p̄` sells (`1 − p̄` in
the low state, `θ(1 − p̄)` in the high state), at `p̄`, allocated in proportion to stock. -/
noncomputable def rpmUnitRevenue (θ pbar Q : ℝ) : ℝ :=
  (1 / 2) * (if pbar ≤ pl Q then pl Q else pbar * (1 - pbar) / Q) +
  (1 / 2) * (if pbar ≤ ph θ Q then ph θ Q else pbar * (θ * (1 - pbar)) / Q)

/-- Expected profit `π_r(t)` of a retailer holding `y = q(t)` units under resale price maintenance
`(p̄, w)` when the retailers' total stock is `Q` (§6.5.2, p. 56). -/
noncomputable def rpmRetailerProfit (θ pbar w Q y : ℝ) : ℝ :=
  y * rpmUnitRevenue θ pbar Q - w * y

/-- Units sold in the low state under a buy-back `b`: the market price cannot fall below `b`, so
the retailers sell `min(q, 1 − b)` (§6.5.2, p. 57). -/
noncomputable def bbSalesLow (b q : ℝ) : ℝ := min q (1 - b)

/-- Units sold in the high state under a buy-back `b`: `min(q, θ(1 − b))` (§6.5.2, p. 57). -/
noncomputable def bbSalesHigh (θ b q : ℝ) : ℝ := min q (θ * (1 - b))

/-- The retailers' expected profit with a buy-back contract `(w, b)` and total order `q`: sales at
the market clearing price, `b` per returned unit, `w` per unit ordered (§6.5.2, p. 57). -/
noncomputable def bbRetailerProfit (θ b w q : ℝ) : ℝ :=
  (1 / 2) * (pl (bbSalesLow b q) * bbSalesLow b q + b * (q - bbSalesLow b q)) +
  (1 / 2) * (ph θ (bbSalesHigh θ b q) * bbSalesHigh θ b q + b * (q - bbSalesHigh θ b q)) -
  w * q

/-- The supplier's expected profit with a buy-back contract `(w, b)` and total order `q`:
`wq` minus the expected buy-back payments; production cost zero (§6.5.2, p. 57). -/
noncomputable def bbSupplierProfit (θ b w q : ℝ) : ℝ :=
  w * q - (1 / 2) * b * (q - bbSalesLow b q) - (1 / 2) * b * (q - bbSalesHigh θ b q)

end CachonCoord.MarketClearing


