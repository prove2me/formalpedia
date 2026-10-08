-- Prove2me | Definitions.Def_RevShareCoord_Single_Model
-- name    : RevShareCoord_Single_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:20:34.429988+00:00
-- url     : https://prove2.me/theorems/99552a74-2942-412b-b48f-994cdb213809
-- title:
--   Sec. 1 — the single-retailer model: strictly concave revenue R(q), unit cost c, and the profits Π, π_r, π_s under a revenue-sharing contract (φ, w)
-- statement:
--   **The single-retailer model.** A supplier sells to one retailer, who orders $q \ge 0$ units before the selling season. The retailer's expected revenue over the season is a function $R(q)$ of the quantity alone; the salvage value of leftover units is normalized to zero. The supplier produces each unit at cost $c > 0$. The standing assumptions are:
--
--   1. $R$ is strictly concave and differentiable for $q \ge 0$, with derivative (marginal revenue) $R'(q)$;
--   2. the product is viable: $R'(0) > c$;
--   3. a finite production quantity is optimal: $R'(\infty) < c$.
--
--   Transactions follow a **revenue-sharing contract** $\{\phi, w\}$: the retailer keeps the share $\phi$ of the revenue, transfers $(1-\phi)R(q)$ to the supplier, and pays the wholesale price $w$ per unit ordered. For an order quantity $q$ the supply chain's, the retailer's and the supplier's profits are
--
--   $$
--   \Pi(q) = R(q) - qc, \qquad \pi_r(q) = \phi R(q) - qw, \qquad \pi_s(q) = (1-\phi)R(q) + qw - qc .
--   $$
--
--   These objects are shared by every statement of the mission: the integrated optimum, the retailer's order decision, and the split of profits under the contract $\{\phi, \phi c\}$.
--
--   **Formalization Note.** $R$ and $R'$ are functions $\mathbb R \to \mathbb R$ constrained only on $q \ge 0$; differentiability is a one-sided derivative within $[0,\infty)$ at every $q \ge 0$, so the derivative at $0$ is the right derivative. "$R'(\infty) < c$" is encoded as "there is $Q \ge 0$ with $R'(Q) < c$": since $R'$ is decreasing, its limit at infinity (possibly $-\infty$) is below $c$ exactly when $R'$ eventually falls below $c$. The paper never displays $\pi_s$ as a formula; it is read off the sequence of events of Sec. 1 (the supplier receives $wq$ and $(1-\phi)R(q)$ and pays $qc$). The contract parameters $\phi, w$ are arguments of the profit functions, unconstrained in the definition; each theorem states the range it needs.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 5 (PDF p. 6), Section 1 (standing assumptions and sequence of events); p. 6 (PDF p. 7), Sections 2.1–2.2 (displays of Π(q) and π_r(q))

import Mathlib

namespace RevShareCoord.Single

/-- The single-retailer model of Sec. 1 (Cachon–Lariviere, June 2000 working paper, p. 5).
`R q` is the retailer's expected revenue from `q` units, `R'` its derivative on `q ≥ 0`
(one-sided at `0`), and `c` the supplier's unit production cost. -/
structure Model where
  /-- Expected revenue `R(q)` as a function of the order quantity. -/
  R : ℝ → ℝ
  /-- Marginal revenue `R'(q)` for `q ≥ 0`. -/
  R' : ℝ → ℝ
  /-- Supplier's unit production cost `c`. -/
  c : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `R` is strictly concave for `q ≥ 0`. -/
  strictConcave : StrictConcaveOn ℝ (Set.Ici 0) R
  /-- `R` is differentiable for `q ≥ 0`, with derivative `R'` (one-sided at `0`). -/
  hasDeriv : ∀ q : ℝ, 0 ≤ q → HasDerivWithinAt R (R' q) (Set.Ici 0) q
  /-- The product is viable: `R'(0) > c`. -/
  viable : c < R' 0
  /-- A finite quantity is optimal, `R'(∞) < c`: marginal revenue eventually falls below `c`. -/
  finite_optimal : ∃ Q : ℝ, 0 ≤ Q ∧ R' Q < c

namespace Model

variable (M : Model)

/-- Total supply chain profit `Π(q) = R(q) − qc` (Sec. 2.1, p. 6). -/
def Pi (q : ℝ) : ℝ := M.R q - q * M.c

/-- Retailer's profit under the revenue-sharing contract `{φ, w}`:
`π_r(q) = φR(q) − qw` (Sec. 2.2, p. 6). -/
def retailerProfit (φ w q : ℝ) : ℝ := φ * M.R q - q * w

/-- Supplier's profit under the revenue-sharing contract `{φ, w}`: she receives `wq` and
`(1 − φ)R(q)` and pays the production cost `qc` (Sec. 1, p. 5, sequence of events). -/
def supplierProfit (φ w q : ℝ) : ℝ := (1 - φ) * M.R q + q * w - q * M.c

end Model

end RevShareCoord.Single


