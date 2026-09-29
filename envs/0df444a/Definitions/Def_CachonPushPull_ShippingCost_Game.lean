-- Prove2me | Definitions.Def_CachonPushPull_ShippingCost_Game
-- name    : CachonPushPull_ShippingCost_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:36:23.926983+00:00
-- url     : https://prove2.me/theorems/e63b567c-db97-4ff3-acc1-460b502fa53e
-- title:
--   The prebook game with at-once shipping cost $\tau$: profits, best responses, outcomes, and "the retailer does not prebook"
-- statement:
--   A contract is a pair of wholesale prices $\{w_1, w_2\}$ (p. 226). Before production the retailer prebooks $y \ge 0$ units at price $w_1$; the supplier then produces $q \ge y$ units at unit cost $c$; during the season the retailer's at-once orders are filled at price $w_2$ from the supplier's remaining stock. The retail price is $p$ and every unit left over is salvaged at $v$. Following §5.1 (p. 234), the supplier pays an extra shipping and handling cost $\tau$ on every unit shipped in an at-once order. With $S$ the expected-sales function:
--
--   1. **Retailer's profit** (p. 233; unchanged by $\tau$):
--   $$
--   \pi_r(y, q) = -(w_1 - v)\,y + (p - v)\,S(y) + (p - w_2)\,\bigl(S(q) - S(y)\bigr).
--   $$
--   2. **Supplier's profit** (Eq. (20) with $w_2$ replaced by her net at-once revenue $w_2 - \tau$):
--   $$
--   \pi_s(y, q) = (w_1 - v)\,y + (w_2 - \tau - v)\,\bigl(S(q) - S(y)\bigr) - (c - v)\,q.
--   $$
--   3. **Supplier best response.** $q$ is a best response to the prebook $y$ if $q \ge y$ and $\pi_s(y, q) \ge \pi_s(y, q')$ for every $q' \ge y$.
--   4. **Outcome.** $(y, q)$ is an outcome of $\{w_1, w_2\}$ if $y \ge 0$, $q$ is a supplier best response to $y$, and $\pi_r(y', q') \le \pi_r(y, q)$ for every $y' \ge 0$ and every supplier best response $q'$ to $y'$: the retailer chooses his prebook anticipating the supplier's production.
--   5. **The retailer does not prebook under the pull contract** $\{w_2, w_2\}$: there is a supplier best response $q_0$ to the prebook $0$, and every positive prebook $y > 0$, followed by any supplier best response $q$ to it, gives the retailer strictly less than $(0, q_0)$:
--   $$
--   \pi_r(y, q) < \pi_r(0, q_0) \quad \text{under } w_1 = w_2 .
--   $$
--
--   These objects are the vocabulary of Theorem 8: a pull contract ($w_1 = w_2 < p$) is compared with advance-purchase discounts ($w_1 < w_2$) at the same at-once price.
--
--   **Formalization Note** The profit formulas are those of §4.5 for contracts with $w_2 \le p$, where at-once orders are submitted; every theorem of the mission assumes $w_2 \le p$ (Theorem 8 assumes $w_2 < p$). The shipping cost $\tau$ enters only the supplier's at-once net revenue. Item 5 is the reading of the paper's "the retailer does not prebook when $w_1 = w_2$" as "$y = 0$ is the retailer's *unique* best reply": with a tie between $y = 0$ and a positive prebook the theorem's conclusion can fail, and the proof's "assume $w_2$ is sufficiently high that the retailer does not prebook" is this strict condition.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 226 (contracts), p. 233, Section 4.5, Eq. (20) and the retailer profit before Eq. (22), p. 234, Section 5.1 and Theorem 8

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Model

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-! ### The prebook game of §4.5 (p. 233) with the at-once shipping cost `τ` of §5.1 (p. 234)

A contract is a pair of wholesale prices `{w₁, w₂}` (p. 226): the retailer prebooks `y ≥ 0` units
at `w₁` before production, the supplier produces `q ≥ y`, and during the season the retailer's
at-once orders are filled at `w₂` from the supplier's remaining stock. The formulas below are
those of §4.5 for contracts with `w₂ ≤ p` (at-once orders are submitted); every theorem of this
mission assumes `w₂ ≤ p`. -/

/-- Retailer's expected profit (p. 233), unchanged by the shipping cost:
`π_r(y, q) = -(w₁ - v) y + (p - v) S(y) + (p - w₂)(S(q) - S(y))`. -/
noncomputable def retailerProfit (μ : Measure ℝ) (p v w₁ w₂ y q : ℝ) : ℝ :=
  -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * (S μ q - S μ y)

/-- Supplier's expected profit with the at-once shipping and handling cost `τ` per unit (§5.1,
p. 234): Eq. (20) with the at-once wholesale price `w₂` replaced by her net revenue `w₂ - τ`,
`π_s(y, q) = (w₁ - v) y + (w₂ - τ - v)(S(q) - S(y)) - (c - v) q`. -/
noncomputable def supplierProfit (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) : ℝ :=
  (w₁ - v) * y + (w₂ - τ - v) * (S μ q - S μ y) - (c - v) * q

/-- `q` is a best response of the supplier to the prebook `y`: `q ≥ y` and `q` maximizes the
supplier's profit over all production quantities `q' ≥ y`. -/
def IsSupplierBestResponse (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) : Prop :=
  y ≤ q ∧ ∀ q' : ℝ, y ≤ q' → supplierProfit μ c v τ w₁ w₂ y q' ≤ supplierProfit μ c v τ w₁ w₂ y q

/-- An outcome `(y, q)` of the contract `{w₁, w₂}`: the prebook `y ≥ 0`, the production `q` is a
supplier best response to `y`, and no other prebook `y' ≥ 0`, followed by any supplier best
response `q'` to it, gives the retailer more than `(y, q)` does (the retailer anticipates the
supplier's response). -/
def IsOutcome (μ : Measure ℝ) (p c v τ w₁ w₂ y q : ℝ) : Prop :=
  0 ≤ y ∧ IsSupplierBestResponse μ c v τ w₁ w₂ y q ∧
    ∀ y' q' : ℝ, 0 ≤ y' → IsSupplierBestResponse μ c v τ w₁ w₂ y' q' →
      retailerProfit μ p v w₁ w₂ y' q' ≤ retailerProfit μ p v w₁ w₂ y q

/-- "The retailer does not prebook when there is no advance-purchase discount" (Theorem 8,
p. 234), for the pull contract `w₁ = w₂`: the supplier has a best response `q₀` to the prebook
`0`, and every positive prebook `y > 0`, followed by any supplier best response `q` to it, gives
the retailer strictly less than prebooking nothing. Equivalently, `y = 0` is the retailer's
unique best reply under `{w₂, w₂}`. -/
def PullNoPrebook (μ : Measure ℝ) (p c v τ w₂ : ℝ) : Prop :=
  ∃ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ ∧
    ∀ y q : ℝ, 0 < y → IsSupplierBestResponse μ c v τ w₂ w₂ y q →
      retailerProfit μ p v w₂ w₂ y q < retailerProfit μ p v w₂ w₂ 0 q₀

end CachonPushPull.ShippingCost


