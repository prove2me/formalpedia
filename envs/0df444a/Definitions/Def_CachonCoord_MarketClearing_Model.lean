-- Prove2me | Definitions.Def_CachonCoord_MarketClearing_Model
-- name    : CachonCoord_MarketClearing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:19:24.441338+00:00
-- url     : https://prove2.me/theorems/cf95404e-6e2e-491c-ab3d-178a33192257
-- title:
--   §6.5.2, pp. 53–55 — market clearing prices p_l, p_h, the competitive retailers' profit, perfect competition, the monopolist's options, q₁, q₂, π_s and w*(θ)
-- statement:
--   This file sets up the model of Deneckere, Marvel and Peck (1997) as presented in §6.5.2. Fix $\theta>1$. Industry demand is low or high, each with probability $1/2$. If the retailers hold a total stock $q$, the market clearing price is
--   $$
--   p_l(q)=(1-q)^+\quad\text{(low state)},\qquad p_h(q)=\Big(1-\frac q\theta\Big)^+\quad\text{(high state)}.
--   $$
--   Leftover inventory has no salvage value and the supplier's production cost is zero.
--
--   1. **Retailers' expected profit.** Under a wholesale price $w$, perfectly competitive retailers who order a total of $q$ units and sell all of them at the market clearing price earn in aggregate
--   $$
--   \pi(q)=\tfrac12p_l(q)q+\tfrac12p_h(q)q-wq .
--   $$
--   2. **Perfect competition.** "The retailers continue to order inventory until their expected profit is zero": a total order $q$ is a *competitive order* for an aggregate expected-profit function $\pi$ if $q>0$, $\pi(q)=0$, and $\pi(x)>0$ for every $0<x<q$.
--   3. **Supplier's outcomes with a wholesale price contract**: the set of profits $wq$ over all $w\in\mathbb R$ and all competitive orders $q$ at $w$.
--   4. **Monopolist's outcomes**: the set of expected profits $\tfrac12p_l(x_l)x_l+\tfrac12p_h(x_h)x_h$ over all stocks $Q$ and sales $0\le x_l\le Q$, $0\le x_h\le Q$ chosen after the state is observed.
--   5. **The page's formulas** (p. 55): $q_1(w)=\frac{2\theta}{1+\theta}(1-w)$, $q_2(w)=\theta(1-2w)$, the threshold $\bar w_0=\tfrac12-\tfrac1{2\theta}$, the supplier's profit $\pi_s(w)=q_1(w)w$ if $w\ge\bar w_0$ and $q_2(w)w$ otherwise, and $w^*(\theta)=1/2$ if $\theta\le3$, $1/4$ otherwise.
--
--   These objects are the common vocabulary of every statement of the mission.
--
--   **Formalization Note** The continuum of retailers indexed by $[0,1]$ enters only through the total order $q$; no measure space of retailers is formalized. The formulas $q_1,q_2,\pi_s,w^*$ are the page's definitions; that they are the competitive order and the optimal price is the content of the theorems, not of this file.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, pp. 53–55 (p_l, p_h pp. 53–54; retailer profit and Π° p. 54; q₁, q₂, π_s, w*(θ) p. 55)

import Mathlib

namespace CachonCoord.MarketClearing

/-- Low-demand market clearing price `p_l(q) = (1 − q)⁺` for the retailers' total stock `q`
(Cachon 2003, 3rd draft, §6.5.2, p. 53). -/
noncomputable def pl (q : ℝ) : ℝ := max (1 - q) 0

/-- High-demand market clearing price `p_h(q) = (1 − q/θ)⁺`, `θ > 1`
(Cachon 2003, 3rd draft, §6.5.2, p. 54). -/
noncomputable def ph (θ q : ℝ) : ℝ := max (1 - q / θ) 0

/-- The perfectly competitive retailers' expected profit under a wholesale price `w`, as a
function of their total order `q`: both states equally likely, all stock sold at the market
clearing price, no salvage value: `(1/2)p_l(q)q + (1/2)p_h(q)q − wq` (§6.5.2, p. 54). -/
noncomputable def retailerProfit (θ w q : ℝ) : ℝ :=
  (1 / 2) * pl q * q + (1 / 2) * ph θ q * q - w * q

/-- Perfect competition (§6.5.2, p. 54: "the retailers continue to order inventory until their
expected profit is zero"): the total order `q > 0` is a competitive outcome of the aggregate
expected-profit function `π` if `π(q) = 0` while `π(x) > 0` for every smaller positive order `x`. -/
def IsCompetitiveOrder (π : ℝ → ℝ) (q : ℝ) : Prop :=
  0 < q ∧ π q = 0 ∧ ∀ x : ℝ, 0 < x → x < q → 0 < π x

/-- The supplier's attainable profits with a wholesale price contract (production cost zero):
the values `w·q` over all wholesale prices `w` and competitive total orders `q` at `w`. -/
def wholesaleOutcomes (θ : ℝ) : Set ℝ :=
  {v | ∃ w q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ∧ v = w * q}

/-- The monopolist's attainable expected profits (§6.5.2, p. 54): she orders a stock `Q`
(production cost zero) and, after observing the state, sells `x_l ∈ [0, Q]` units in the low state
and `x_h ∈ [0, Q]` in the high state at the market clearing prices; unsold units are worthless. -/
def monopolyOutcomes (θ : ℝ) : Set ℝ :=
  {v | ∃ Q xl xh : ℝ, 0 ≤ xl ∧ xl ≤ Q ∧ 0 ≤ xh ∧ xh ≤ Q ∧
    v = (1 / 2) * pl xl * xl + (1 / 2) * ph θ xh * xh}

/-- `q₁(w) = (2θ/(1 + θ))(1 − w)` (§6.5.2, p. 55). -/
noncomputable def q1 (θ w : ℝ) : ℝ := (2 * θ / (1 + θ)) * (1 - w)

/-- `q₂(w) = θ(1 − 2w)` (§6.5.2, p. 55). -/
noncomputable def q2 (θ w : ℝ) : ℝ := θ * (1 - 2 * w)

/-- The branch threshold `(1/2) − 1/(2θ)` of p. 55. -/
noncomputable def wBar0 (θ : ℝ) : ℝ := 1 / 2 - 1 / (2 * θ)

/-- The supplier's profit `π_s(w)` as displayed on p. 55: `q₁(w)w` if `w ≥ (1/2) − 1/(2θ)`,
`q₂(w)w` otherwise. -/
noncomputable def supplierProfit (θ w : ℝ) : ℝ :=
  if wBar0 θ ≤ w then q1 θ w * w else q2 θ w * w

/-- The page's `w*(θ)`: `1/2` if `θ ≤ 3`, `1/4` otherwise (p. 55). -/
noncomputable def wStar (θ : ℝ) : ℝ := if θ ≤ 3 then 1 / 2 else 1 / 4

end CachonCoord.MarketClearing


