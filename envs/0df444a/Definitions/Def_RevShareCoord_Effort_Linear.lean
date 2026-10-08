-- Prove2me | Definitions.Def_RevShareCoord_Effort_Linear
-- name    : RevShareCoord_Effort_Linear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:43.027404+00:00
-- url     : https://prove2.me/theorems/27dae95a-4c12-4c76-9499-51a6c84a623d
-- title:
--   Sec. 4.2.2 — the linear example P(q, e) = 1 − q + 2τe, g(e) = e²: profits, the retailer's response, w(φ), p_I and the supplier's value V(φ)
-- statement:
--   **The linear-demand example.** Fix a parameter $\tau \ge 0$ (the impact of effort on demand) and a unit cost $c$. The retailer faces the inverse demand curve and earns the revenue
--
--   $$
--   P(q, e) = 1 - q + 2\tau e, \qquad R(q, e) = q\,P(q, e),
--   $$
--
--   and pays the effort cost $g(e) = e^2$. Under the contract $\{\phi, w\}$ the retailer's profit is $\pi_r(q, e) = \phi R(q, e) - e^2 - qw$, the supplier's profit is $(1-\phi)R(q, e) + q(w - c)$, and the integrated channel's profit is $\Pi(q, e) = R(q, e) - e^2 - qc$. The retailer chooses $(q, e)$ in the quadrant $q \ge 0$, $e \ge 0$; a pair is an **optimal response** to $\{\phi, w\}$ if it maximizes $\pi_r$ jointly over the quadrant.
--
--   The page's closed forms are recorded as definitions:
--
--   1. the effort rule $e(q) = \phi\tau q$;
--   2. the order rule $q(w, \phi) = (\phi - w)/(2(\phi - \phi^2\tau^2))$ if $w < \phi$, and $q(w, \phi) = 0$ otherwise;
--   3. the supplier's profit $\pi_s(w, \phi) = (1-\phi)R\big(q(w,\phi), e(q(w,\phi))\big) + q(w,\phi)(w - c)$;
--   4. the wholesale price $w(\phi) = \phi\big((1-\tau^2)\phi + c(1-\phi\tau^2)\big)/\big(1 + \phi(1-2\tau^2)\big)$;
--   5. the integrated retail price $p_I = P\big(q(c, 1), e(q(c, 1))\big)$.
--
--   Finally, the set of the supplier's attainable profits with share $\phi$ collects $(1-\phi)R(q, e) + q(w-c)$ over all wholesale prices $w \ge 0$ and all optimal responses $(q, e)$ of the retailer to $\{\phi, w\}$, and the supplier's value $V(\phi)$ is its supremum.
--
--   These definitions carry the example: the theorems prove that the closed forms are the optima they stand for, and compare $V(\phi)$ across shares.
--
--   **Formalization Note.** The closed forms are only definitions; that they are the retailer's and the supplier's optima is proved in the theorems, never assumed. $V(\phi)$ is a real supremum, which Lean sets to $0$ on an empty or unbounded set; the goal theorem shows the set has a greatest element for every $\phi \in (0, 1]$, so no such default is used. The order rule divides by $\phi - \phi^2\tau^2$, which vanishes at $\phi = 0$; every theorem takes $\phi \in (0, 1]$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 23 (PDF p. 24), Section 4.2.2 (P(q, e), R(q, e), g(e), π_r(q, e), e(q), q(w, φ)); p. 24 (PDF p. 25), Section 4.2.2 (p_I, π_s(w, φ), w(φ))

import Mathlib

namespace RevShareCoord.Effort

/-! The linear-demand example of Sec. 4.2.2 (Cachon–Lariviere, June 2000 working paper,
pp. 23–24): inverse demand `P(q, e) = 1 − q + 2τe`, revenue `R(q, e) = qP(q, e)`, effort cost
`g(e) = e²`. Quantities and efforts range over `[0, ∞)`. -/

namespace Linear

/-- The retailer's decision set `{(q, e) : q ≥ 0, e ≥ 0}`. -/
def quadrant : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Ici 0

/-- Inverse demand `P(q, e) = 1 − q + 2τe`. -/
def price (τ q e : ℝ) : ℝ := 1 - q + 2 * τ * e

/-- Expected revenue `R(q, e) = qP(q, e)`. -/
def revenue (τ q e : ℝ) : ℝ := q * price τ q e

/-- The retailer's profit `π_r(q, e) = φR(q, e) − e² − qw`. -/
def retailerProfit (τ φ w q e : ℝ) : ℝ := φ * revenue τ q e - e ^ 2 - q * w

/-- The supplier's profit `(1 − φ)R(q, e) + q(w − c)` when the retailer chooses `(q, e)`. -/
def supplierProfit (τ c φ w q e : ℝ) : ℝ := (1 - φ) * revenue τ q e + q * (w - c)

/-- The integrated channel's profit `Π(q, e) = R(q, e) − e² − qc`. -/
def channelProfit (τ c q e : ℝ) : ℝ := revenue τ q e - e ^ 2 - q * c

/-- `x = (q, e)` is an optimal response of the retailer to the contract `{φ, w}`: it maximizes
`π_r` over all `q ≥ 0`, `e ≥ 0`, jointly. -/
def IsRetailerResponse (τ φ w : ℝ) (x : ℝ × ℝ) : Prop :=
  x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => retailerProfit τ φ w y.1 y.2) quadrant x

/-- The page's effort rule `e(q) = φτq`. -/
def effort (τ φ q : ℝ) : ℝ := φ * τ * q

/-- The page's order rule `q(w, φ) = (φ − w)/(2(φ − φ²τ²))` if `w < φ`, otherwise `0`. -/
noncomputable def orderQty (τ φ w : ℝ) : ℝ :=
  if w < φ then (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) else 0

/-- The supplier's profit `π_s(w, φ) = (1 − φ)R(q(w, φ), e(q(w, φ))) + q(w, φ)(w − c)`. -/
noncomputable def supplierProfitAt (τ c φ w : ℝ) : ℝ :=
  supplierProfit τ c φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w))

/-- The page's wholesale price `w(φ) = φ((1 − τ²)φ + c(1 − φτ²))/(1 + φ(1 − 2τ²))`. -/
noncomputable def wholesalePrice (τ c φ : ℝ) : ℝ :=
  φ * ((1 - τ ^ 2) * φ + c * (1 - φ * τ ^ 2)) / (1 + φ * (1 - 2 * τ ^ 2))

/-- The retail price of the integrated channel, `P` at the retailer's solution with `w = c`,
`φ = 1`. -/
noncomputable def integratedPrice (τ c : ℝ) : ℝ :=
  price τ (orderQty τ 1 c) (effort τ 1 (orderQty τ 1 c))

/-- The supplier's profits attainable with the share `φ`: the profit `(1 − φ)R(q, e) + q(w − c)`
for some wholesale price `w ≥ 0` and some optimal response `(q, e)` of the retailer to `{φ, w}`. -/
def supplierOutcomes (τ c φ : ℝ) : Set ℝ :=
  {s | ∃ w : ℝ, 0 ≤ w ∧ ∃ x : ℝ × ℝ, IsRetailerResponse τ φ w x ∧
    s = supplierProfit τ c φ w x.1 x.2}

/-- The supplier's optimal profit with the share `φ`, `V(φ) = sup_{w ≥ 0} π_s(w, φ)`. -/
noncomputable def supplierValue (τ c φ : ℝ) : ℝ := sSup (supplierOutcomes τ c φ)

end Linear

end RevShareCoord.Effort


