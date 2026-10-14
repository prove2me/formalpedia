-- Prove2me | Definitions.Def_CostlyShort_ShortMarket_Setting
-- name    : CostlyShort_ShortMarket_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:43.26708+00:00
-- url     : https://prove2.me/theorems/8611c19e-63ce-4020-a269-4cb5df5bc3be
-- title:
--   §2.5–§3.2, pp. 14–17 — lending fees (3), the mean-variance problem (8), the portfolios (9), revenue (10), equilibrium (Definition 1)
-- statement:
--   This module fixes the objects of §2.5–§3.2 of Evgeniou, Hugonnier and Prieto, at a single state $(\omega,t)$ of their continuous-time economy; the time index is dropped. There are a riskless asset, two risky assets with volatilities $\sigma_1,\sigma_2$, two agents $a\in\{o,p\}$ (optimist and pessimist), and a single lending agent who sets the shorting cost of asset 1. Rates are measured per unit of volatility of asset 1: the lending yield is $\gamma=\Gamma/\sigma_1$ and the shorting cost is $\phi=\Phi/\sigma_1$.
--
--   1. **Lending fees** (3), p. 14. A position $m$ in asset 1 earns or pays fees at the rate
--   $$\Lambda(m;\Phi,\Gamma)=m^+\Gamma-m^-\Phi,\qquad m^+=\max\{m,0\},\ m^-=\max\{-m,0\}.$$
--   2. **Mean-variance problem** (8), p. 16. Agent $a$ with market prices of risk $\theta_1,\theta_2$ chooses wealth fractions $p=(p_1,p_2)\in\mathbb R\times\mathbb R_+$ to maximize
--   $$\Lambda(p_1;\Phi,\Gamma)+p_1\sigma_1\theta_1+p_2\sigma_2\theta_2-\tfrac12(p_1\sigma_1+p_2\sigma_2)^2 .$$
--   A portfolio is *optimal* if $p_2\ge0$ and no $q\in\mathbb R\times\mathbb R_+$ gives a larger value.
--   3. **Proposition 1 portfolios** (9a)–(9b), p. 17. A portfolio $p$ is of the form (9) if for some real $x$, with $0\le x\le\theta_2$ whenever $\theta_2\ge0$,
--   $$p_1\sigma_1=\mathbb 1_{\{\theta_2\ge0\}}x+\mathbb 1_{\{\theta_1+\phi\le0\}}(\theta_1+\phi),\qquad p_2\sigma_2=\mathbb 1_{\{\theta_2\ge0\}}(\theta_2-x).$$
--   4. **Lending revenue** (10), p. 17. At shorting cost $y$ per unit of volatility the lending agent's revenue, divided by $\sigma_1$, is
--   $$R(y)=y\,(\theta^{(o)}_1+y)^-W^{(o)}+y\,(\theta^{(p)}_1+y)^-W^{(p)} .$$
--   5. **Equilibrium at a state** (Definition 1, pp. 14–15, with (7) of p. 16). The tuple $(\sigma_1,\sigma_2,S_1,W^{(o)},W^{(p)},\theta^{(o)}_1,\theta^{(p)}_1,\theta^{(o)}_2,\theta^{(p)}_2,\gamma,\phi,p^{(o)},p^{(p)})$ is an equilibrium if
--      - $\theta^{(a)}_2=\theta^{(a)}_1+\gamma$ for both agents (7);
--      - $p^{(a)}$ is optimal in (8) for agent $a$, with $\Phi=\phi\sigma_1$, $\Gamma=\gamma\sigma_1$;
--      - asset 1 clears: $W^{(o)}p^{(o)}_1+W^{(p)}p^{(p)}_1=S_1$;
--      - the lending market clears: $\sum_a\Lambda(W^{(a)}p^{(a)}_1;\Phi,\Gamma)=0$;
--      - $\phi$ is the least element of $\operatorname{argmax}_{y\ge\gamma}R(y)$ — condition (4), in the per-volatility form (10), with the paper's selection (13).
--
--   These are the instantaneous equilibrium conditions from which §3.2 derives the shorting cost and the lending yield.
--
--   **Formalization Note** Dollar positions are $\pi^{(a)}_1=W^{(a)}p^{(a)}_1$ (p. 16). The single lending agent ($n\equiv1$, p. 14) is built in. Condition (4) is stated over $y\ge\gamma$ because (10) is "well-defined only if $\phi\ge\gamma$" (p. 17); the least maximizer is the selection the paper makes in (13). Consumption clearing and asset-2 clearing are omitted, since no result of this mission uses them. In (9) the constraint $0\le x\le\theta_2$ is imposed only when $\theta_2\ge0$: as printed it has no solution when $\theta_2<0$, where $x$ is multiplied by $0$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), pp. 14–17, (3), Definition 1 (4)–(5), (7), (8), (9a)–(9b), (10), (13)

import Mathlib

namespace CostlyShort.ShortMarket

/-- (3), p. 14: the flow rate of lending fees of a position `m` in asset 1,
`Λ(m; Φ, Γ) = m⁺ Γ − m⁻ Φ`, with `m⁺ = max m 0` and `m⁻ = max (-m) 0`. -/
def lendingFlow (Φ Γ m : ℝ) : ℝ := max m 0 * Γ - max (-m) 0 * Φ

/-- (8), p. 16: the objective of an agent's mean-variance problem in the wealth fractions
`p = (p₁, p₂)` invested in the two risky assets, given volatilities `σ₁ σ₂`, the dollar shorting
cost `Φ`, the dollar lending yield `Γ` and the agent's market prices of risk `θ₁ θ₂`:
`Λ(p₁; Φ, Γ) + Σᵢ pᵢ σᵢ θᵢ − ½ (p₁ σ₁ + p₂ σ₂)²`. -/
noncomputable def mvObjective (σ₁ σ₂ Φ Γ θ₁ θ₂ : ℝ) (p : ℝ × ℝ) : ℝ :=
  lendingFlow Φ Γ p.1 + (p.1 * σ₁ * θ₁ + p.2 * σ₂ * θ₂) - (p.1 * σ₁ + p.2 * σ₂) ^ 2 / 2

/-- `p ∈ ℝ × ℝ₊` solves the mean-variance problem (8), p. 16. -/
def IsOptimalFractions (σ₁ σ₂ Φ Γ θ₁ θ₂ : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.2 ∧ ∀ q : ℝ × ℝ, 0 ≤ q.2 → mvObjective σ₁ σ₂ Φ Γ θ₁ θ₂ q ≤ mvObjective σ₁ σ₂ Φ Γ θ₁ θ₂ p

/-- (9a)–(9b), p. 17: the portfolios described by Proposition 1, with `φ` the shorting cost per
unit of volatility. The free number `x` is constrained to `[0, θ₂]` only when `θ₂ ≥ 0`, the only
case in which it enters. -/
def IsProp1Portfolio (σ₁ σ₂ φ θ₁ θ₂ : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ x : ℝ, (0 ≤ θ₂ → 0 ≤ x ∧ x ≤ θ₂) ∧
    p.1 * σ₁ = (if 0 ≤ θ₂ then x else 0) + (if θ₁ + φ ≤ 0 then θ₁ + φ else 0) ∧
    p.2 * σ₂ = (if 0 ≤ θ₂ then θ₂ - x else 0)

/-- (10), p. 17 (right-hand side): the lending agent's revenue per unit of volatility when the
shorting cost per unit of volatility is `y`, `Σₐ y (θ₁⁽ᵃ⁾ + y)⁻ W⁽ᵃ⁾`. -/
def lendingRevenue (θ₁o θ₁p Wo Wp y : ℝ) : ℝ :=
  y * max (-(θ₁o + y)) 0 * Wo + y * max (-(θ₁p + y)) 0 * Wp

/-- Definition 1, pp. 14–15, at one state: condition (7) for both agents, optimal wealth fractions
`po`, `pp` of the optimist and the pessimist (problem (8) at `Φ = φ σ₁`, `Γ = γ σ₁`), clearing of
the market for asset 1 and of the lending market (5) with dollar positions `W⁽ᵃ⁾ p₁⁽ᵃ⁾`, and the
shorting cost (4) taken in its per-volatility form (10) over `y ≥ γ`, as the least maximizer (13). -/
structure IsShortMarketEquilibrium (σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ : ℝ) (po pp : ℝ × ℝ) :
    Prop where
  eq7_o : θ₂o = θ₁o + γ
  eq7_p : θ₂p = θ₁p + γ
  opt_o : IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁o θ₂o po
  opt_p : IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁p θ₂p pp
  clear_asset1 : Wo * po.1 + Wp * pp.1 = S₁
  clear_lending :
    lendingFlow (φ * σ₁) (γ * σ₁) (Wo * po.1) + lendingFlow (φ * σ₁) (γ * σ₁) (Wp * pp.1) = 0
  cost : IsLeast {y | γ ≤ y ∧ ∀ z, γ ≤ z →
    lendingRevenue θ₁o θ₁p Wo Wp z ≤ lendingRevenue θ₁o θ₁p Wo Wp y} φ

end CostlyShort.ShortMarket


