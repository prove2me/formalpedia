-- Prove2me | Definitions.Def_SeasonalPricing_Shared_LambdaI
-- name    : SeasonalPricing_Shared_LambdaI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:14:27.452065+00:00
-- url     : https://prove2.me/theorems/aea1dbad-b378-4457-89ba-055c6d071d29
-- title:
--   Segment rates $\Lambda_I$, $\Lambda_W$, $\Lambda_L$ of the contingent pricing model (§4.2)
-- statement:
--   Customers arrive to the store as a Poisson process with rate $\lambda$ during the season $[0, H]$; the premium price $p_1$ applies on $[0, T)$ and the discount price $p_2$ from time $T$ on. A customer with base valuation $V$ arriving at time $t$ has valuation $V e^{-\alpha t}$, and $\bar F$ denotes the tail of the base valuation. Given a purchasing threshold $\psi(t)$ for customers arriving at time $t < T$ (they buy at arrival iff their valuation is at least $\psi(t)$), the paper splits the customers into groups whose sizes are Poisson with the following means.
--
--   1. Customers arriving during $[0, T]$ who buy immediately at $p_1$ (group I):
--   $$
--   \Lambda_I(\psi) = \lambda \int_0^T \bar F\big(\psi(t) e^{\alpha t}\big)\,dt .
--   $$
--   2. Customers arriving during $[0, T]$ whose valuation on arrival is below $p_1$ and who want to buy at the discount price $p_2$ at time $T$ (group W):
--   $$
--   \Lambda_W(p_1, p_2) = \lambda \int_0^T \Big[\bar F\big(\min\{p_1 e^{\alpha t},\, p_2 e^{\alpha T}\}\big) - \bar F\big(p_1 e^{\alpha t}\big)\Big]\,dt .
--   $$
--   3. Customers arriving during $[T, H]$ whose valuation is at least $p_2$ (group L):
--   $$
--   \Lambda_L(p_2) = \lambda \int_T^H \bar F\big(p_2 e^{\alpha t}\big)\,dt .
--   $$
--
--   These rates are the building blocks of every expected-revenue expression of the paper. With myopic customers the threshold is the premium price itself, $\psi \equiv p_1$. This definition is shared by two missions of this series: 3 (optimal contingent-pricing revenue with myopic customers and exponential valuations: §6, p. 349, and Proposition 3, p. 350, with its proof on pp. 358–359) and 4 (optimal prices and discount time with myopic customers and identical declining valuations: Proposition 4, p. 351, with its proof on p. 359).
--
--   **Formalization Note** The three rates are `LambdaI`, `LambdaW`, `LambdaL`, defined for an arbitrary function $\bar F : \mathbb R \to \mathbb R$ and arbitrary real parameters (arrival rate, decline factor, discount time, horizon), as interval integrals `∫ t in a..b`. Lean's interval integral of a non-integrable function is $0$; each mission that uses the rates fixes a bounded measurable tail. The strategic group S of the paper ($\Lambda_S$) is not needed for myopic customers and is not defined here.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 343, §3 (V_j(t) = V_j e^{−αt}); p. 345, §4.2 (Λ_I(ψ), Λ_W(p1, p2)); p. 346, §4.2 (Λ_L(p2))

import Mathlib

namespace SeasonalPricing.Shared

/-- `Λ_I(ψ) ≐ λ ∫_{t=0}^{T} F̄(ψ(t) e^{αt}) dt` (Aviv–Pazgal 2008, §4.2, p. 345): the mean number
of customers arriving during `[0, T]` (Poisson rate `λ`, base valuation tail `F̄`, valuation
`V e^{−αt}` at time `t`) who buy immediately at the premium price, when customers arriving at
time `t` buy iff their current valuation is at least the threshold `ψ(t)`. -/
noncomputable def LambdaI (lam α T : ℝ) (Fbar : ℝ → ℝ) (ψ : ℝ → ℝ) : ℝ :=
  lam * ∫ t in (0)..T, Fbar (ψ t * Real.exp (α * t))

/-- `Λ_W(p₁, p₂) ≐ λ ∫_{t=0}^{T} [F̄(min{p₁e^{αt}, p₂e^{αT}}) − F̄(p₁e^{αt})] dt`
(Aviv–Pazgal 2008, §4.2, p. 345): the mean number of customers arriving during `[0, T]` whose
valuation on arrival is below the premium price `p₁` and who want to buy at the discount price
`p₂` at time `T`. -/
noncomputable def LambdaW (lam α T : ℝ) (Fbar : ℝ → ℝ) (p1 p2 : ℝ) : ℝ :=
  lam * ∫ t in (0)..T,
    (Fbar (min (p1 * Real.exp (α * t)) (p2 * Real.exp (α * T))) - Fbar (p1 * Real.exp (α * t)))

/-- `Λ_L(p₂) ≐ λ ∫_{t=T}^{H} F̄(p₂ e^{αt}) dt` (Aviv–Pazgal 2008, §4.2, p. 346): the mean number
of customers arriving during `[T, H]` whose valuation is at least the discount price `p₂`. -/
noncomputable def LambdaL (lam α T H : ℝ) (Fbar : ℝ → ℝ) (p2 : ℝ) : ℝ :=
  lam * ∫ t in T..H, Fbar (p2 * Real.exp (α * t))

end SeasonalPricing.Shared


