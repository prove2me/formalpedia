-- Prove2me | Definitions.Def_UtilityTokens_ICOChoice_Setting
-- name    : UtilityTokens_ICOChoice_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:32.800983+00:00
-- url     : https://prove2.me/theorems/14022753-313c-465c-a67f-204a8594b6b0
-- title:
--   §§4–6, (1), (3), (6)–(11), (16) — active share, basic utility, threshold prices, traditional-sales and ICO demands and profits, optimal payoffs, θ*, Θ̃ and x̄
-- statement:
--   A monopolist (the entrepreneur) sells a digital product with network effects to a unit mass of consumers whose types $\theta$ are uniform on $[0,\Theta]$, with $\Theta>1$. The network intensity is $x>0$, and an ICO costs $f>0$. The entrepreneur's choice is written, as in the paper, as a **threshold type** $\bar\theta\in[1,\Theta]$: exactly the types $\theta\ge\bar\theta$ become active users, so the share of active users is
--   $$a(\bar\theta)=\frac{\Theta-\bar\theta}{\Theta},$$
--   basic users get $v=a\,x$ (display (1)), and the price is $p=\bar\theta v$. At $\bar\theta=1$ this is $p=v$, the non-discriminatory price.
--
--   The definitions are:
--
--   1. **Traditional sales.** Demand (3) is $Q(p^T_1)=1$ at $p^T_1=v$ ($\bar\theta=1$) and $Q(p^T_1)=(\Theta-\bar\theta)/\Theta$ at $p^T_1=\bar\theta v\in(v,\Theta v]$ ($\bar\theta>1$). The profit is $X_T(\bar\theta)=p^T_1\,Q(p^T_1)$, i.e. (6) at $\bar\theta=1$ and (7) for $\bar\theta>1$.
--   2. **ICO.** The token price is $p^I_0=\bar\theta v$ with token demand (8), the same two-piece formula as (3). The late price $p^I_1$ is a separate choice; late demand (9) is $Q(p^I_1)=1-Q(p^I_0)$ if $p^I_1=v$ and $0$ otherwise. The profit is the objective of (10),
--   $$X_I(\bar\theta,p^I_1)=p^I_0\,Q(p^I_0)+p^I_1\,Q(p^I_1)-f .$$
--   The ICO strategies are the pairs $(\bar\theta,p^I_1)$ with $\bar\theta\in[1,\Theta]$ and $p^I_1\in[v,\Theta v]$, where $v$ is computed at $\bar\theta$ (footnote 7 restricts every price to $[v,\Theta v]$).
--   3. **Optimal payoffs.** $X^*_T=\sup_{\bar\theta\in[1,\Theta]}X_T(\bar\theta)$ and $X^*_I=\sup X_I$ over the ICO strategies.
--   4. **Closed forms.** The interior root $\theta_{\mathrm{int}}(\Theta)=\bigl(2\Theta+1-\sqrt{\Theta^2+\Theta+1}\bigr)/3$, the threshold $\theta^*=\max[1,\theta_{\mathrm{int}}(\Theta)]$ of (11), $\tilde\Theta=(\sqrt5+3)/2$ (p. 22),
--   $$F(\Theta)=(\theta^*-1)\Bigl[\Bigl(\frac{\Theta-\theta^*}{\Theta}\Bigr)^2-\frac1\Theta\Bigr],\qquad \bar x=\frac{f}{F(\Theta)}\quad\text{(p. 23, Appendix A).}$$
--
--   These objects are shared by every statement of the mission: the propositions compare the two optimal payoffs and locate the threshold $\bar x$.
--
--   **Formalization Note** The paper derives (3), (8) and (9) from the consumers' participation constraints and the fixed point $v=a x$; that derivation, the consumer types as a probability distribution and the timing are not formalized, and the demands and payoffs are taken as the model's primitives. The paper recasts prices as thresholds, $p=\bar\theta v$ with $v$ depending on $\bar\theta$; the definitions do the same, so the choice variable is $\bar\theta$ (and $p^I_1$), not a posted price. $X^*_T$ and $X^*_I$ are real suprema (`sSup`), meaningful for $\Theta>1$, where the strategy sets are nonempty and the profits bounded. $F$ and $\bar x$ are total functions: $F(\Theta)=0$ for $1<\Theta\le\tilde\Theta$ and then $\bar x=0$, so every statement about $\bar x$ restricts to $\Theta>\tilde\Theta$. The demands (3) and (8) are separate definitions with the same formula because the paper displays them separately.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), pp. 13–23, §4, §5.1, §5.2, §6, (1), (3), (6)–(11), (16), footnote 7 (p. 16); p. 35, Appendix A

import Mathlib

namespace UtilityTokens.ICOChoice

/-- The share `a = (Θ - θ̄)/Θ` of active users when exactly the types `θ ≥ θ̄` of
`U[0, Θ]` are active. -/
noncomputable def activeShare (Θ θbar : ℝ) : ℝ := (Θ - θbar) / Θ

/-- The basic users' utility `v = a x`, display (1), with `a = activeShare Θ θbar`. -/
noncomputable def basicUtility (Θ x θbar : ℝ) : ℝ := activeShare Θ θbar * x

/-- The threshold price `p = θ̄ v` (the price `p₁ᵀ` of traditional sales, p. 17, and the
token price `p₀ᴵ` of the ICO, p. 21). At `θbar = 1` it is `p = v`. -/
noncomputable def thresholdPrice (Θ x θbar : ℝ) : ℝ := θbar * basicUtility Θ x θbar

/-- Demand under traditional sales, display (3): `1` at `p₁ᵀ = v` (`θbar = 1`), and
`(Θ - θ̄)/Θ` at `p₁ᵀ = θ̄ v ∈ (v, Θ v]` (`θbar > 1`). -/
noncomputable def demandT (Θ θbar : ℝ) : ℝ := if θbar = 1 then 1 else activeShare Θ θbar

/-- Traditional-sales profit `p₁ᵀ Q(p₁ᵀ)`: display (6) at `θbar = 1`, display (7) for
`θbar > 1`. -/
noncomputable def profitT (Θ x θbar : ℝ) : ℝ := thresholdPrice Θ x θbar * demandT Θ θbar

/-- Token demand at `t = 0` under the ICO, display (8). -/
noncomputable def demandI0 (Θ θbar : ℝ) : ℝ := if θbar = 1 then 1 else activeShare Θ θbar

/-- Demand at `t = 1` under the ICO, display (9): the residual `1 - Q(p₀ᴵ)` at
`p₁ᴵ = v`, and `0` at `p₁ᴵ ∈ (v, Θ v]`. -/
noncomputable def demandI1 (Θ x θbar p1 : ℝ) : ℝ :=
  if p1 = basicUtility Θ x θbar then 1 - demandI0 Θ θbar else 0

/-- ICO profit `p₀ᴵ Q(p₀ᴵ) + p₁ᴵ Q(p₁ᴵ) - f`, the objective of (10), with
`p₀ᴵ = θ̄ v`. -/
noncomputable def profitI (Θ x f θbar p1 : ℝ) : ℝ :=
  thresholdPrice Θ x θbar * demandI0 Θ θbar + p1 * demandI1 Θ x θbar p1 - f

/-- The ICO strategies `(θ̄, p₁ᴵ)`: `θ̄ ∈ [1, Θ]` (so `p₀ᴵ = θ̄ v ∈ [v, Θ v]`) and
`p₁ᴵ ∈ [v, Θ v]` (footnote 7, p. 16). -/
def ICOChoices (Θ x : ℝ) : Set (ℝ × ℝ) :=
  {c | c.1 ∈ Set.Icc 1 Θ ∧ c.2 ∈ Set.Icc (basicUtility Θ x c.1) (Θ * basicUtility Θ x c.1)}

/-- The optimal traditional-sales payoff `X*_T`: the supremum of `profitT` over the
thresholds `θ̄ ∈ [1, Θ]`. -/
noncomputable def optPayoffT (Θ x : ℝ) : ℝ := sSup (profitT Θ x '' Set.Icc 1 Θ)

/-- The optimal ICO payoff `X*_I`: the supremum of `profitI` over the ICO strategies. -/
noncomputable def optPayoffI (Θ x f : ℝ) : ℝ :=
  sSup ((fun c : ℝ × ℝ => profitI Θ x f c.1 c.2) '' ICOChoices Θ x)

/-- The interior root `(2Θ + 1 - √(Θ² + Θ + 1))/3`, the second argument of the `Max`
in (11). -/
noncomputable def thetaInterior (Θ : ℝ) : ℝ := (2 * Θ + 1 - Real.sqrt (Θ ^ 2 + Θ + 1)) / 3

/-- `θ* = max[1, (2Θ + 1 - √(Θ² + Θ + 1))/3]`, display (11). -/
noncomputable def thetaStar (Θ : ℝ) : ℝ := max 1 (thetaInterior Θ)

/-- `Θ̃ = (√5 + 3)/2`, p. 22. -/
noncomputable def thetaTilde : ℝ := (Real.sqrt 5 + 3) / 2

/-- `F(Θ) = (θ* - 1)[((Θ - θ*)/Θ)² - 1/Θ]`, the denominator of `x̄` (Appendix A). -/
noncomputable def Fden (Θ : ℝ) : ℝ := (thetaStar Θ - 1) * (((Θ - thetaStar Θ) / Θ) ^ 2 - 1 / Θ)

/-- The threshold network intensity `x̄ = f / F(Θ)`, p. 23. -/
noncomputable def xbar (Θ f : ℝ) : ℝ := f / Fden Θ

end UtilityTokens.ICOChoice


