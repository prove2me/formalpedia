-- Prove2me | Definitions.Def_ChannelRebate_NoCoord_Setting
-- name    : ChannelRebate_NoCoord_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:20:31.029052+00:00
-- url     : https://prove2.me/theorems/23453058-e520-4566-b25b-7705a8c7d3c0
-- title:
--   §3.1, §4.1, §4.3, pp. 994–1000 — demand density (A4), Φ, Γ, effort cost (A5), Π(Q, e), R(Q, e|T), r_b(Q|T) and optimal pairs
-- statement:
--   This file fixes the quantity-and-effort model of Taylor (2002), §4, in which a retailer chooses an order quantity $Q \ge 0$ and a sales effort $e \ge 0$ before random demand is observed.
--
--   1. **Demand (Assumption A4, p. 994).** The base demand $\xi$ has a probability density $\varphi$ on $\mathbb R$ with $\varphi(\xi) = 0$ for $\xi < 0$, $\varphi(\xi) > 0$ for all $\xi \ge 0$, $\int \varphi = 1$ and finite mean $\int \xi\,\varphi(\xi)\,d\xi < \infty$. Its distribution function and partial first moment are
--   $$\Phi(Q) = \int_0^Q \varphi(\xi)\,d\xi, \qquad \Gamma(Q) = \int_0^Q \xi\, d\Phi(\xi).$$
--   Under effort $e$ demand is $e\xi$ (§4.1, p. 999); its law is the image of the law of $\xi$ under $x \mapsto ex$.
--   2. **Effort cost (Assumption A5, p. 999).** The cost of effort $V$ satisfies $V(0) = 0$ and is strictly increasing and strictly convex on $[0, \infty)$ (the paper states on p. 995 that every function described as convex or increasing is strictly so). It is differentiable at every $e > 0$ with derivative $V'(e)$.
--   3. **Integrated channel (p. 999).** With unit cost $c$, retail price $p$ and salvage value $s$,
--   $$\Pi(Q, e) = -cQ + pE\min(Q, e\xi) + sE(Q - e\xi)^+ - V(e).$$
--   4. **Retailer under a target rebate and returns (§4.3, p. 1000).** With wholesale price $w$, rebate $u$ per unit sold beyond the target $T$, and return credit $b$ per unsold unit,
--   $$R(Q, e \mid T) = -wQ + pE\min(Q, e\xi) + uE(\min(Q, e\xi) - T)^+ + bE(Q - e\xi)^+ - V(e).$$
--   Returns alone is the case $u = 0$; a target rebate alone is the case $b = s$; a linear rebate is the target rebate with $T = 0$.
--   5. **Quantity-only profit at unit effort (§3.2, p. 995, with $b$ in place of $s$).**
--   $$r_b(Q \mid T) = -wQ + pE\min(Q, \xi) + bE(Q - \xi)^+ + uE(\min(Q, \xi) - T)^+ .$$
--   The threshold $\tau$ of Lemma 2 is the root on $[\underline Q_0, \underline Q_1]$ of $T \mapsto r_b(\underline Q_0 \mid T) - r_b(\underline Q_1 \mid T)$.
--   6. **Optimality.** A pair $(Q, e)$ is optimal for a profit function $f$ when $Q \ge 0$, $e \ge 0$ and $f(Q, e) \ge f(Q', e')$ for all $Q' \ge 0$, $e' \ge 0$; an order $Q$ is optimal for $g$ when $Q \ge 0$ and $g(Q) \ge g(Q')$ for all $Q' \ge 0$.
--
--   These objects are shared by every statement of the mission: the first-order conditions of the integrated channel, Lemma 2, the kink of the retailer's effort objective, and Proposition 2.
--
--   **Formalization Note** The expectations $E\min(Q, e\xi)$ and $E(Q - e\xi)^+$ are the published `CachonCoord.Newsvendor.expSales` and `expLeftover` applied to the image law of $e\xi$; the rebate term is the integral of $\max(\min(Q, x) - T, 0)$ against the same law. The derivative $V'$ is carried as a field of the effort-cost structure together with `HasDerivAt V (V' e) e` for every $e > 0$: the paper writes $(\partial/\partial e)V(e)$ in every first-order condition without stating differentiability. The same model is restated in the sibling missions of this paper, because draft definitions cannot import each other.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 994, Assumptions A1, A4; p. 995, §3.1–3.2 (Φ, Γ, r(Q|T), strictness convention); p. 999, §4.1, Assumption A5 and Π(Q, e); p. 1000, §4.3, R(Q, e|T)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory ProbabilityTheory

namespace ChannelRebate.NoCoord

/-- Demand `ξ` under Assumption A4 (Taylor 2002, p. 994): a probability density `φ` on `ℝ`
that vanishes on `(-∞, 0)` and is strictly positive on `[0, ∞)`, with finite mean. -/
structure Demand where
  φ : ℝ → ℝ
  measurable_φ : Measurable φ
  φ_neg : ∀ ξ, ξ < 0 → φ ξ = 0
  φ_pos : ∀ ξ, 0 ≤ ξ → 0 < φ ξ
  integrable_φ : Integrable φ
  integral_φ : ∫ ξ, φ ξ = 1
  integrable_mul_φ : Integrable (fun ξ => ξ * φ ξ)

/-- The law of `ξ`: Lebesgue measure with density `φ`. -/
noncomputable def Demand.law (D : Demand) : Measure ℝ :=
  volume.withDensity (fun ξ => ENNReal.ofReal (D.φ ξ))

/-- The law of the effort-scaled demand `e ξ`: the image of the law of `ξ` under `x ↦ e x`. -/
noncomputable def Demand.effLaw (D : Demand) (e : ℝ) : Measure ℝ :=
  D.law.map (fun x => e * x)

/-- The distribution function `Φ(Q) = ∫₀^Q φ(ξ) dξ` (p. 994). -/
noncomputable def Phi (D : Demand) (Q : ℝ) : ℝ := ∫ ξ in (0)..Q, D.φ ξ

/-- `Γ(Q) = ∫₀^Q ξ dΦ(ξ)` (p. 995). -/
noncomputable def Gam (D : Demand) (Q : ℝ) : ℝ := ∫ ξ in (0)..Q, ξ * D.φ ξ

/-- The cost of effort under Assumption A5 (p. 999): `V(0) = 0`, `V` strictly increasing and
strictly convex on `[0, ∞)` ("all functions described as convex, increasing ... are strictly so",
p. 995). The paper writes `(∂/∂e)V(e)` in every first-order condition; the derivative `dV` with
`HasDerivAt V (dV e) e` for every `e > 0` is a disclosed differentiability hypothesis. -/
structure EffortCost where
  V : ℝ → ℝ
  V_zero : V 0 = 0
  strictMonoOn : StrictMonoOn V (Set.Ici 0)
  strictConvexOn : StrictConvexOn ℝ (Set.Ici 0) V
  dV : ℝ → ℝ
  hasDerivAt : ∀ e, 0 < e → HasDerivAt V (dV e) e

/-- The integrated channel's profit (§4.1, p. 999):
`Π(Q, e) = −cQ + pE min(Q, eξ) + sE(Q − eξ)⁺ − V(e)`. -/
noncomputable def chainProfit (p c s : ℝ) (D : Demand) (V : EffortCost) (Q e : ℝ) : ℝ :=
  -c * Q + p * CachonCoord.Newsvendor.expSales (D.effLaw e) Q
    + s * CachonCoord.Newsvendor.expLeftover (D.effLaw e) Q - V.V e

/-- The expected rebate base `E(min(Q, eξ) − T)⁺`. -/
noncomputable def expRebate (D : Demand) (e T Q : ℝ) : ℝ :=
  ∫ x, max (min Q x - T) 0 ∂(D.effLaw e)

/-- The retailer's profit under a target rebate `(w, u, T)` with return credit `b` (§4.3, p. 1000):
`R(Q, e|T) = −wQ + pE min(Q, eξ) + uE(min(Q, eξ) − T)⁺ + bE(Q − eξ)⁺ − V(e)`.
Returns alone is `u = 0`; a target rebate alone is `b = s`; a linear rebate is `T = 0`. -/
noncomputable def retailerProfit (p w u b T : ℝ) (D : Demand) (V : EffortCost) (Q e : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales (D.effLaw e) Q + u * expRebate D e T Q
    + b * CachonCoord.Newsvendor.expLeftover (D.effLaw e) Q - V.V e

/-- The retailer's quantity-only profit at unit effort with salvage (return credit) `b`
(§3.2, p. 995, with `b` in place of `s`):
`r_b(Q|T) = −wQ + pE min(Q, ξ) + bE(Q − ξ)⁺ + uE(min(Q, ξ) − T)⁺`.
The threshold `τ` of Lemma 2 is the root of `r_b(Q̲₀|T) − r_b(Q̲₁|T)` on `[Q̲₀, Q̲₁]`. -/
noncomputable def quantityProfit (p w u b : ℝ) (D : Demand) (T Q : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales D.law Q
    + b * CachonCoord.Newsvendor.expLeftover D.law Q
    + u * ∫ x, max (min Q x - T) 0 ∂D.law

/-- The set of optimal order quantities of `g` over `Q ≥ 0`. -/
def optimalOrders (g : ℝ → ℝ) : Set ℝ :=
  {Q | 0 ≤ Q ∧ ∀ Q', 0 ≤ Q' → g Q' ≤ g Q}

end ChannelRebate.NoCoord


