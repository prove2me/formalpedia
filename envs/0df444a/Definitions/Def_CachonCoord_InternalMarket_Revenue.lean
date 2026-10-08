-- Prove2me | Definitions.Def_CachonCoord_InternalMarket_Revenue
-- name    : CachonCoord_InternalMarket_Revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:50.033758+00:00
-- url     : https://prove2.me/theorems/2bede6c9-9677-4c56-8026-79d4926a83bf
-- title:
--   §6.9.1, pp. 92–93 — retailer revenue π(γ, α, Q), the share γ°(α) of (44), π(α, Q), retailer profit π_i(q_i, w) and the price w(α, Q)
-- statement:
--   The deterministic objects of the internal-market model of §6.9.1, for a fixed realization. Let $\eta>1$ be the constant demand elasticity, $\alpha_1,\alpha_2>0$ the realized demand levels of the two retailers, and $Q\ge 0$ the realized output. Retailer $i$ selling $q_i$ units earns $q_ip_i(q_i)$ with the inverse demand $p_i(q_i)=\alpha_iq_i^{-1/\eta}$. All powers are real powers.
--
--   1. **Total retailer revenue** when retailer one receives $\gamma Q$ units and retailer two $(1-\gamma)Q$ units:
--   $$
--   \pi(\gamma,\alpha,Q)=\big(\alpha_1\gamma^{(\eta-1)/\eta}+\alpha_2(1-\gamma)^{(\eta-1)/\eta}\big)Q^{(\eta-1)/\eta}.
--   $$
--   2. **The share** of (44): $\gamma^o(\alpha)=\alpha_1^\eta/(\alpha_1^\eta+\alpha_2^\eta)$.
--   3. **Revenue under that allocation**: $\pi(\alpha,Q)=\pi(\gamma^o(\alpha),\alpha,Q)$.
--   4. **Retailer $i$'s profit** at the per-unit price $w$: $\pi_i(q_i,w)=\alpha_iq_i^{(\eta-1)/\eta}-wq_i$.
--   5. **The contingent price**
--   $$
--   w(\alpha,Q)=\Big(\frac{\eta-1}{\eta}\Big)(\alpha_1^\eta+\alpha_2^\eta)^{1/\eta}Q^{-1/\eta}.
--   $$
--
--   These are the objects of every deterministic statement of the mission: that $\gamma^o(\alpha)$ is the optimal share, the closed form of $\pi(\alpha,Q)$, and that $w(\alpha,Q)$ clears the market, are theorems, not definitions.
--
--   **Formalization Note** The formulas are meant for $\gamma\in[0,1]$, $Q\ge0$ (and $Q>0$ for the price); outside that range Lean's real power returns junk values, and every theorem restricts to the range. $\gamma^o(\alpha)$ is the printed formula, not an argmax.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 92 (π(γ, α, Q), p_i) and p. 93 (Eq. (44), π(α, Q), π_i(q_i, w), w(α, Q))

import Mathlib

namespace CachonCoord.InternalMarket

/-- Total retailer revenue `π(γ, α, Q)` (Cachon 2003, 3rd draft, §6.9.1, p. 92) when retailer one
receives `γQ` units and retailer two `(1 − γ)Q` units of the output `Q`:
`π(γ, α, Q) = (α₁ γ^{(η−1)/η} + α₂ (1 − γ)^{(η−1)/η}) Q^{(η−1)/η}`.
Here `η > 1` is the constant demand elasticity and `α₁, α₂ > 0` the demand realizations;
all powers are real powers (`Real.rpow`), meant for `γ ∈ [0, 1]` and `Q ≥ 0`. -/
noncomputable def revenue (η α₁ α₂ γ Q : ℝ) : ℝ :=
  (α₁ * γ ^ ((η - 1) / η) + α₂ * (1 - γ) ^ ((η - 1) / η)) * Q ^ ((η - 1) / η)

/-- The share `γ°(α) = α₁^η / (α₁^η + α₂^η)` of output allocated to retailer one, Eq. (44)
(§6.9.1, p. 93). Defined by the printed formula; that it is the optimal share is a theorem. -/
noncomputable def optShare (η α₁ α₂ : ℝ) : ℝ :=
  α₁ ^ η / (α₁ ^ η + α₂ ^ η)

/-- Total retailer revenue conditional on the allocation `γ°(α)`:
`π(α, Q) = π(γ°(α), α, Q)` (§6.9.1, p. 93). Its closed form is a theorem. -/
noncomputable def optRevenue (η α₁ α₂ Q : ℝ) : ℝ :=
  revenue η α₁ α₂ (optShare η α₁ α₂) Q

/-- Retailer `i`'s profit when he buys `qᵢ` units at the per-unit price `w` and has demand
realization `αᵢ` (§6.9.1, p. 93): `πᵢ(qᵢ, w) = αᵢ qᵢ^{(η−1)/η} − w qᵢ`
(revenue `qᵢ pᵢ(qᵢ)` with `pᵢ(qᵢ) = αᵢ qᵢ^{−1/η}`, p. 92). Meant for `qᵢ ≥ 0`. -/
noncomputable def retailerProfit (η αᵢ w q : ℝ) : ℝ :=
  αᵢ * q ^ ((η - 1) / η) - w * q

/-- The contingent transfer price
`w(α, Q) = ((η − 1)/η) (α₁^η + α₂^η)^{1/η} Q^{−1/η}` (§6.9.1, p. 93), meant for `Q > 0`. -/
noncomputable def price (η α₁ α₂ Q : ℝ) : ℝ :=
  ((η - 1) / η) * (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ (-1 / η)

end CachonCoord.InternalMarket


