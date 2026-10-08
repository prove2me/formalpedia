-- Prove2me | Definitions.Def_ChannelRebate_Quantity_Setting
-- name    : ChannelRebate_Quantity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:13.049516+00:00
-- url     : https://prove2.me/theorems/13609844-424b-4104-8ca2-c1e01216b883
-- title:
--   §3.1–3.2, pp. 994–996 — demand density (A4), Φ, Γ, the target-rebate profit r(Q|T), manufacturer and channel profits
-- statement:
--   This file fixes the quantity-only model of Taylor (2002), §3.
--
--   **Demand.** Demand $\xi$ is a nonnegative random variable with a density $\varphi$: $\varphi$ is measurable, $\varphi(x) = 0$ for $x < 0$, $\varphi(x) > 0$ for every $x \ge 0$ (Assumption A4), $\int \varphi = 1$, and $\xi$ has a finite mean ($x \mapsto x\varphi(x)$ is integrable). The law of $\xi$ is Lebesgue measure with density $\varphi$. Write
--   $$
--   \Phi(Q) = \int_0^Q \varphi(x)\,dx, \qquad \Gamma(Q) = \int_0^Q x\,\varphi(x)\,dx = \int_0^Q \xi\, d\Phi(\xi).
--   $$
--
--   **Profits.** Let $p$ be the retail price, $c$ the manufacturing cost, $s$ the salvage value, $w$ the wholesale price, $u$ the channel rebate and $T$ the target level. For an order quantity $Q$:
--   1. the integrated channel earns $\pi(Q) = -cQ + pE\min(Q,\xi) + sE(Q-\xi)^+$;
--   2. the retailer under a wholesale price-only contract earns $-wQ + pE\min(Q,\xi) + sE(Q-\xi)^+$;
--   3. the retailer under the target rebate $(w,u,T)$ earns
--   $$
--   r(Q\mid T) = -wQ + pE\min(Q,\xi) + sE(Q-\xi)^+ + uE(\min(Q,\xi)-T)^+;
--   $$
--   4. the manufacturer earns $m(Q\mid T) = (w-c)Q - uE(\min(Q,\xi)-T)^+$: she sells $Q$ units at $w$, produces them at $c$, and pays $u$ for each unit the retailer sells beyond $T$.
--
--   The rebate level $\hat u(w) = (w-c)(p-s)/(c-s)$ is the one used in Theorem 1. An order $Q^*$ is **optimal** for a profit function $f$ when $Q^* \ge 0$ and $f(Q) \le f(Q^*)$ for every $Q \ge 0$; the set of optimal orders is written $\arg\max_{Q\ge 0} f$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $E\min(Q,\xi)$ and $E(Q-\xi)^+$ are `expSales` and `expLeftover` of the published definition `CachonCoord_Newsvendor_Contracts`, applied to the law of $\xi$. The manufacturer's profit is defined by its own formula, not as the channel profit minus the retailer's.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), pp. 994–996, Assumptions A1–A4, §3.1–3.2; û(w) p. 996; manufacturer profit as in the proof of Proposition 1, p. 1005

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Demand `ξ` of Taylor (2002), §3.1, p. 994: a random variable with density `φ`.
Assumption A4: `φ(ξ) > 0` for all `ξ ≥ 0`. Demand is nonnegative (`φ = 0` on `(-∞, 0)`),
`φ` is a probability density, and demand has a finite mean. -/
structure Demand where
  φ : ℝ → ℝ
  measurable_φ : Measurable φ
  φ_eq_zero_of_neg : ∀ x : ℝ, x < 0 → φ x = 0
  φ_pos : ∀ x : ℝ, 0 ≤ x → 0 < φ x
  integrable_φ : Integrable φ
  integral_φ : ∫ x, φ x = 1
  integrable_mul_φ : Integrable (fun x => x * φ x)

/-- The law of demand: Lebesgue measure with density `φ`. -/
noncomputable def Demand.law (D : Demand) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (D.φ x))

/-- The distribution function `Φ(Q) = ∫₀^Q φ(ξ) dξ` (p. 994). -/
noncomputable def Phi (D : Demand) (Q : ℝ) : ℝ := ∫ x in (0 : ℝ)..Q, D.φ x

/-- `Γ(Q) = ∫₀^Q ξ dΦ(ξ)` (p. 995). -/
noncomputable def Gam (D : Demand) (Q : ℝ) : ℝ := ∫ x in (0 : ℝ)..Q, x * D.φ x

/-- Expected units sold beyond the target, `E(min(Q, ξ) − T)⁺` (p. 995). -/
noncomputable def rebateUnits (D : Demand) (Q T : ℝ) : ℝ :=
  ∫ x, max (min Q x - T) 0 ∂D.law

/-- Integrated-channel profit `π(Q) = −cQ + pE min(Q, ξ) + sE(Q − ξ)⁺` (p. 995). -/
noncomputable def chainProfit (p c s : ℝ) (D : Demand) (Q : ℝ) : ℝ :=
  -c * Q + p * CachonCoord.Newsvendor.expSales D.law Q
    + s * CachonCoord.Newsvendor.expLeftover D.law Q

/-- Retailer profit under a wholesale price-only contract,
`−wQ + pE min(Q, ξ) + sE(Q − ξ)⁺` (p. 995). -/
noncomputable def wholesaleProfit (p s w : ℝ) (D : Demand) (Q : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales D.law Q
    + s * CachonCoord.Newsvendor.expLeftover D.law Q

/-- Retailer profit under the target rebate `(w, u, T)`,
`r(Q|T) = −wQ + pE min(Q, ξ) + sE(Q − ξ)⁺ + uE(min(Q, ξ) − T)⁺` (p. 995). -/
noncomputable def retailerProfit (p s w u T : ℝ) (D : Demand) (Q : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales D.law Q
    + s * CachonCoord.Newsvendor.expLeftover D.law Q + u * rebateUnits D Q T

/-- Manufacturer profit under the target rebate `(w, u, T)`: `(w − c)Q − uE(min(Q, ξ) − T)⁺`. -/
noncomputable def manufProfit (c w u T : ℝ) (D : Demand) (Q : ℝ) : ℝ :=
  (w - c) * Q - u * rebateUnits D Q T

/-- `û(w) = (w − c)(p − s)/(c − s)` (p. 996). -/
noncomputable def uHat (p c s w : ℝ) : ℝ := (w - c) * (p - s) / (c - s)

/-- `Q` is an optimal order for the profit function `f`: it maximizes `f` over `Q ≥ 0`. -/
def IsOptimalOrder (f : ℝ → ℝ) (Q : ℝ) : Prop := 0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' → f Q' ≤ f Q

/-- The set of optimal orders of `f`. -/
def optimalOrders (f : ℝ → ℝ) : Set ℝ := {Q | IsOptimalOrder f Q}

end ChannelRebate.Quantity


