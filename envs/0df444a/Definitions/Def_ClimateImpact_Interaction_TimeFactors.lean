-- Prove2me | Definitions.Def_ClimateImpact_Interaction_TimeFactors
-- name    : ClimateImpact_Interaction_TimeFactors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:32.027643+00:00
-- url     : https://prove2.me/theorems/799aee93-38a3-4626-b038-f3e525c54464
-- title:
--   Proposition 2 (12), p. 19, and Corollary 3 (13), p. 20 — time factors β_t, β^c_t, quadratic externality κ₀ − (κ/2)x², rate ψ^{*,i}_t
-- statement:
--   The time factors and the no-interaction emission rate of De Angelis, Tankov and Zerbib.
--
--   Let $\rho$ be the rate of time preference and $T>0$ the final date. For $t\in[0,T]$ the **companies' time factor** and the **green investors' time factor** of Proposition 2, (12), are
--   $$\beta^c_t=\frac{e^{-\rho t}-e^{-\rho T}}{1-e^{-\rho T}},\qquad \beta_t=\frac{1-e^{-\rho t}}{1-e^{-\rho T}} .$$
--   For $\rho,T>0$ both lie in $[0,1]$ on $[0,T]$ and $\beta_t+\beta^c_t=1$; $\beta_0=0$ and $\beta^c_T=0$.
--
--   The **quadratic climate externality** of Corollary 3 is $\theta(x)=\kappa_0-\frac{\kappa}{2}x^2$, and the **optimal emission rate without interaction effect**, (13), is
--   $$\psi^{*,i}_t=\frac{c^i_t}{\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t},$$
--   where $c^i_t$ is company $i$'s marginal abatement cost, $\alpha$ the green investors' wealth share, and $\kappa_t,\kappa^c_t$ the sensitivities of green investors and of companies to the externality.
--
--   These objects are shared by every statement of the series.
--
--   **Formalization Note** The functions take the parameters $(\rho,T,t)$, resp. $(\rho,T,\alpha,\kappa,\kappa^c,c,t)$, as real numbers; Lean's division returns $0$ on a zero denominator, so every statement that uses them assumes $\rho,T>0$, $t\in[0,T]$, $0<\alpha<1$ and $\kappa_t,\kappa^c_t>0$ (standing assumptions of §2 and Corollary 3), under which no denominator vanishes: $1-e^{-\rho T}>0$, and since $\beta_t+\beta^c_t=1$ with both nonnegative, $\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t>0$ even at $t=0$ ($\beta_0=0$) and $t=T$ ($\beta^c_T=0$). The externality $\theta$ is defined on all of $\mathbb R$; the page's domain $x\ge0$ is imposed by the statements that use it. The externality parameters are passed as numbers at a fixed date $t$, so the same functions serve the time-dependent $\kappa_t,\kappa^c_t,\kappa_{0,t}$ of the paper and the company-independent constants of footnote 15.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 2 (12), p. 19; Corollary 3 (13), p. 20

import Mathlib

namespace ClimateImpact.Interaction

/-- The companies' time factor `β^c_t = (e^{-ρt} - e^{-ρT}) / (1 - e^{-ρT})` of Proposition 2, (12)
(SSRN 3562534, p. 19). -/
noncomputable def betaC (ρ T t : ℝ) : ℝ :=
  (Real.exp (-(ρ * t)) - Real.exp (-(ρ * T))) / (1 - Real.exp (-(ρ * T)))

/-- The green investors' time factor `β_t = (1 - e^{-ρt}) / (1 - e^{-ρT})` of Proposition 2, (12)
(p. 19). -/
noncomputable def beta (ρ T t : ℝ) : ℝ :=
  (1 - Real.exp (-(ρ * t))) / (1 - Real.exp (-(ρ * T)))

/-- The quadratic climate externality of Corollary 3 (p. 20): `θ(x) = κ₀ - (κ/2) x²`. -/
noncomputable def quadExt (κ₀ κ x : ℝ) : ℝ :=
  κ₀ - κ / 2 * x ^ 2

/-- The optimal emission rate (13) of Corollary 3 (p. 20):
`ψ^{*,i}_t = c^i_t / (β^c_t κ^c_t + α β_t κ_t)`. -/
noncomputable def noInteractionRate (ρ T α κ κc c t : ℝ) : ℝ :=
  c / (betaC ρ T t * κc + α * beta ρ T t * κ)

end ClimateImpact.Interaction


