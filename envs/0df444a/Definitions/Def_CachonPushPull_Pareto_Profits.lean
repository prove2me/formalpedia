-- Prove2me | Definitions.Def_CachonPushPull_Pareto_Profits
-- name    : CachonPushPull_Pareto_Profits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:22:41.834677+00:00
-- url     : https://prove2.me/theorems/3a3d68e5-74e3-4de5-928e-039d99d472d5
-- title:
--   Push and pull contract profits, the inducing wholesale prices $\hat w_1(q)$, $w_1(q)$, and the prebook game behind the push challenge
-- statement:
--   Prices are the retail price $p$, the production cost $c$ and the salvage value $v$. The paper assumes $v < c < p$; these are hypotheses of the theorems, not of the definitions.
--
--   **Push contracts** (a single wholesale price $\hat w_1$; the retailer prebooks $q$ and bears all inventory risk). The retailer's and supplier's expected profits are
--   $$
--   \hat\pi_r(q, \hat w_1) = (p - v) S(q) - (\hat w_1 - v) q, \qquad \hat\pi_s(q, \hat w_1) = (\hat w_1 - c) q .
--   $$
--   The price that induces the prebook $q$ (Eq. (3)) is $\hat w_1(q) = p - (p - v) F(q)$, and $\hat\pi_r(q) = \hat\pi_r(q, \hat w_1(q))$, $\hat\pi_s(q) = \hat\pi_s(q, \hat w_1(q))$.
--
--   **Pull contracts** (a single wholesale price $w_1 = w_2$; the retailer does not prebook, the supplier produces $q$ and bears all inventory risk). The expected profits are
--   $$
--   \pi_s(q, w_1) = (w_1 - v) S(q) - (c - v) q, \qquad \pi_r(q, w_1) = (p - w_1) S(q).
--   $$
--   The price that induces the production $q$ (Eqs. (7)–(8)) is $w_1(q) = \dfrac{c - v F(q)}{1 - F(q)}$, and $\pi_s(q) = \pi_s(q, w_1(q))$, $\pi_r(q) = \pi_r(q, w_1(q))$.
--
--   **The prebook game** (§4.5). Under wholesale prices $(w_1, w_2)$ the retailer prebooks $y \ge 0$, then the supplier produces $Q \ge y$. The supplier's profit is (Eq. (20))
--   $$
--   \pi_s(y, Q) = (w_1 - v) y + (w_2 - v)\big(S(Q) - S(y)\big) - (c - v) Q,
--   $$
--   and $Q$ is a *best reply* to $y$ if $Q \ge y$ and $Q$ maximizes $\pi_s(y, \cdot)$ over all $Q' \ge y$. The retailer's profit is
--   $$
--   \pi_r(y, Q) = -(w_1 - v) y + (p - v) S(y) + (p - w_2)\big(S(Q) - S(y)\big),
--   $$
--   which for $Q = y$ is the push profit $(p - v)S(y) - (w_1 - v) y$.
--
--   **Push challenge.** The pull contract with quantity $q$ (so $w_1 = w_2 = w_1(q)$) *survives the push challenge* if (a) for every $y \ge 0$ the supplier has a best reply, and (b) for every $y > 0$, every best reply $Q$ to $y$ and every best reply $Q_0$ to $0$,
--   $$
--   \pi_r(y, Q) < \pi_r(0, Q_0),
--   $$
--   that is, the retailer strictly prefers to prebook nothing.
--
--   These definitions are the payoff functions compared in the Pareto analysis of §4.4 and the game that certifies the pull contracts are actually played as pull.
--
--   **Formalization Note** Every profit is defined in the paper's primitive form (quantity, price) and composed with the inducing price; the closed forms (4), (6), (13) are theorems, not definitions. Survival is defined from the game itself, with the supplier's replies quantified as maximizers of (20), and not from the formula $\pi_r(q)$. The paper reads "prefers … rather than … any positive amount" as strict preference, which is what its proof establishes.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, pp. 227-228 (Section 4.2 Eq. (3), Section 4.3 Eqs. (7)-(8), (13)), p. 228 (push challenge), p. 231 (Lemma 5), p. 233 (Section 4.5, Eq. (20) and the retailer's profit)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-! ### Push contracts (§4.2, p. 227) -/

/-- Push retailer's expected profit with prebook `q` at wholesale price `ŵ₁ = w`:
`π̂_r(q, ŵ₁) = (p - v) S(q) - (ŵ₁ - v) q`. -/
noncomputable def pushRetailerProfitAt (μ : Measure ℝ) (p v w q : ℝ) : ℝ :=
  (p - v) * S μ q - (w - v) * q

/-- Push supplier's profit `π̂_s(q, ŵ₁) = (ŵ₁ - c) q`. -/
def pushSupplierProfitAt (c w q : ℝ) : ℝ :=
  (w - c) * q

/-- The push wholesale price that induces prebook `q`, solved from Eq. (3):
`ŵ₁(q) = p - (p - v) F(q)`. -/
noncomputable def pushPrice (μ : Measure ℝ) (p v q : ℝ) : ℝ :=
  p - (p - v) * cdf μ q

/-- `π̂_r(q) = π̂_r(q, ŵ₁(q))`. -/
noncomputable def pushRetailerProfit (μ : Measure ℝ) (p v q : ℝ) : ℝ :=
  pushRetailerProfitAt μ p v (pushPrice μ p v q) q

/-- `π̂_s(q) = π̂_s(q, ŵ₁(q))`. -/
noncomputable def pushSupplierProfit (μ : Measure ℝ) (p c v q : ℝ) : ℝ :=
  pushSupplierProfitAt c (pushPrice μ p v q) q

/-! ### Pull contracts (§4.3, pp. 227–228) -/

/-- Pull supplier's expected profit with production `q` at wholesale price `w₁ = w₂ = w`:
`π_s(q, w₁) = (w₁ - v) S(q) - (c - v) q`. -/
noncomputable def pullSupplierProfitAt (μ : Measure ℝ) (c v w q : ℝ) : ℝ :=
  (w - v) * S μ q - (c - v) * q

/-- Pull retailer's expected profit `π_r(q, w₁) = (p - w₁) S(q)`. -/
noncomputable def pullRetailerProfitAt (μ : Measure ℝ) (p w q : ℝ) : ℝ :=
  (p - w) * S μ q

/-- The pull wholesale price that induces production `q`, solved from Eq. (7) (Eq. (8)):
`w₁(q) = (c - v F(q)) / (1 - F(q))`. -/
noncomputable def pullPrice (μ : Measure ℝ) (c v q : ℝ) : ℝ :=
  (c - v * cdf μ q) / (1 - cdf μ q)

/-- `π_s(q) = π_s(q, w₁(q))`. -/
noncomputable def pullSupplierProfit (μ : Measure ℝ) (c v q : ℝ) : ℝ :=
  pullSupplierProfitAt μ c v (pullPrice μ c v q) q

/-- `π_r(q) = π_r(q, w₁(q))`. -/
noncomputable def pullRetailerProfit (μ : Measure ℝ) (p c v q : ℝ) : ℝ :=
  pullRetailerProfitAt μ p (pullPrice μ c v q) q

/-! ### The prebook game with wholesale prices `(w₁, w₂)` (§4.5, p. 233) -/

/-- Supplier's profit when the retailer prebooks `y` and the supplier produces `Q ≥ y` (Eq. (20)):
`π_s(y, Q) = (w₁ - v) y + (w₂ - v)(S(Q) - S(y)) - (c - v) Q`. -/
noncomputable def apdSupplierProfit (μ : Measure ℝ) (c v w₁ w₂ y Q : ℝ) : ℝ :=
  (w₁ - v) * y + (w₂ - v) * (S μ Q - S μ y) - (c - v) * Q

/-- `Q` is an optimal production quantity for the supplier given prebook `y`: `Q ≥ y` and `Q`
maximizes `apdSupplierProfit` over all production quantities `Q' ≥ y`. -/
def IsSupplierBestReply (μ : Measure ℝ) (c v w₁ w₂ y Q : ℝ) : Prop :=
  y ≤ Q ∧ ∀ Q' : ℝ, y ≤ Q' → apdSupplierProfit μ c v w₁ w₂ y Q' ≤ apdSupplierProfit μ c v w₁ w₂ y Q

/-- Retailer's expected profit when he prebooks `y` and the supplier produces `Q ≥ y`:
`-(w₁ - v) y + (p - v) S(y) + (p - w₂)(S(Q) - S(y))` (p. 233). For `Q = y` this is the push
profit `(p - v) S(y) - (w₁ - v) y`. -/
noncomputable def apdRetailerProfit (μ : Measure ℝ) (p v w₁ w₂ y Q : ℝ) : ℝ :=
  -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * (S μ Q - S μ y)

/-- The pull contract with production `q` (single wholesale price `w₁ = w₂ = w₁(q)`) survives the
push challenge (pp. 228, 231): for every prebook `y ≥ 0` the supplier has an optimal production
reply, and every positive prebook `y > 0`, followed by an optimal supplier reply, leaves the
retailer with strictly less expected profit than prebooking zero, followed by an optimal supplier
reply. -/
def SurvivesPushChallenge (μ : Measure ℝ) (p c v q : ℝ) : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∃ Q : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) y Q) ∧
  ∀ y Q Q₀ : ℝ, 0 < y →
    IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) y Q →
    IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ →
    apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) y Q <
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀

end CachonPushPull.Pareto


