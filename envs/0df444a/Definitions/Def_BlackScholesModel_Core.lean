-- Prove2me | Definitions.Def_BlackScholesModel_Core
-- name    : BlackScholesModel_Core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:46.58742+00:00
-- url     : https://prove2.me/theorems/a9720361-6dac-4022-b3b0-13676e5ec155
-- title:
--   Black–Scholes model: normal CDF/PDF, $d_\pm$, call and put prices
-- statement:
--   Core definitions of the Black–Scholes model for a non-dividend-paying stock. Throughout, $K$ is the strike, $T$ the expiry, $r$ the risk-free rate, $\sigma$ the volatility, $S$ the spot price, $t$ the current time and $\tau=T-t$ the time to maturity.
--
--   1. Standard normal distribution and density functions:
--   $$N(x)=\frac1{\sqrt{2\pi}}\int_{-\infty}^x e^{-z^2/2}\,dz,\qquad N'(x)=\frac1{\sqrt{2\pi}}e^{-x^2/2}.$$
--   2. The Black–Scholes parameters
--   $$d_+=\frac{\ln(S/K)+(r+\sigma^2/2)\tau}{\sigma\sqrt\tau},\qquad d_-=d_+-\sigma\sqrt\tau .$$
--   3. The call and put prices
--   $$C(S,t)=N(d_+)S-N(d_-)Ke^{-r(T-t)},\qquad P(S,t)=N(-d_-)Ke^{-r(T-t)}-N(-d_+)S .$$
--   4. The alternative (Black '76) formulation with discount factor $D$ and forward price $F$:
--   $$d_\pm=\frac{\ln(F/K)\pm\sigma^2\tau/2}{\sigma\sqrt\tau},\qquad C(F,\tau)=D\,[N(d_+)F-N(d_-)K],\qquad P(F,\tau)=D\,[N(-d_-)K-N(-d_+)F].$$
--   5. The risk-neutral terminal stock price driven by a standard normal sample $z$:
--   $$S_T(z)=S\exp\Big(\big(r-\tfrac{\sigma^2}2\big)\tau+\sigma\sqrt\tau\,z\Big).$$
--
--   These definitions are shared by every theorem of the mission.
--
--   **Formalization Note** The functions are total: outside the model's domain ($S\le0$, $K\le0$, $\sigma\le0$ or $\tau\le0$) the logarithm, square root and division take Lean's default values, so statements about them always carry the hypotheses $K>0$, $\sigma>0$, $S>0$, $t<T$ where needed.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 3 (Notation), pp. 3–5 (Black–Scholes formula, Alternative formulation), p. 6 (risk-neutral stock price)

import Mathlib

namespace BlackScholesModel

open Real MeasureTheory

/-- The standard normal cumulative distribution function
`N(x) = (1/√(2π)) ∫_{-∞}^x e^{-z²/2} dz`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2)

/-- The standard normal probability density function `N'(x) = (1/√(2π)) e^{-x²/2}`. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x ^ 2 / 2)

/-- `d₊ = (ln(S/K) + (r + σ²/2) τ) / (σ √τ)`, where `τ = T - t` is the time to maturity. -/
noncomputable def dPlus (S K r σ τ : ℝ) : ℝ :=
  (Real.log (S / K) + (r + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ)

/-- `d₋ = d₊ - σ √τ`. -/
noncomputable def dMinus (S K r σ τ : ℝ) : ℝ :=
  dPlus S K r σ τ - σ * Real.sqrt τ

/-- Black–Scholes price at time `t` of a European call with strike `K`, expiry `T`,
risk-free rate `r` and volatility `σ`, on a non-dividend-paying stock with spot price `S`:
`C(S, t) = N(d₊) S - N(d₋) K e^{-r(T-t)}`. -/
noncomputable def callPrice (K r σ T : ℝ) (S t : ℝ) : ℝ :=
  stdNormalCDF (dPlus S K r σ (T - t)) * S
    - stdNormalCDF (dMinus S K r σ (T - t)) * K * Real.exp (-r * (T - t))

/-- Black–Scholes price at time `t` of the corresponding European put:
`P(S, t) = N(-d₋) K e^{-r(T-t)} - N(-d₊) S`. -/
noncomputable def putPrice (K r σ T : ℝ) (S t : ℝ) : ℝ :=
  stdNormalCDF (-dMinus S K r σ (T - t)) * K * Real.exp (-r * (T - t))
    - stdNormalCDF (-dPlus S K r σ (T - t)) * S

/-- Forward-form `d₊ = (ln(F/K) + σ² τ / 2) / (σ √τ)` (Black '76 parameters). -/
noncomputable def dPlusFwd (F K σ τ : ℝ) : ℝ :=
  (Real.log (F / K) + σ ^ 2 * τ / 2) / (σ * Real.sqrt τ)

/-- Forward-form `d₋ = d₊ - σ √τ`. -/
noncomputable def dMinusFwd (F K σ τ : ℝ) : ℝ :=
  dPlusFwd F K σ τ - σ * Real.sqrt τ

/-- Call value in the alternative (Black '76) formulation:
`C(F, τ) = D [N(d₊) F - N(d₋) K]`, with discount factor `D` and forward price `F`. -/
noncomputable def callPriceFwd (D F K σ τ : ℝ) : ℝ :=
  D * (stdNormalCDF (dPlusFwd F K σ τ) * F - stdNormalCDF (dMinusFwd F K σ τ) * K)

/-- Put value in the alternative (Black '76) formulation:
`P(F, τ) = D [N(-d₋) K - N(-d₊) F]`. -/
noncomputable def putPriceFwd (D F K σ τ : ℝ) : ℝ :=
  D * (stdNormalCDF (-dMinusFwd F K σ τ) * K - stdNormalCDF (-dPlusFwd F K σ τ) * F)

/-- Risk-neutral terminal stock price, as a function of a standard normal sample `z`:
`S_T = S exp((r - σ²/2) τ + σ √τ z)`. -/
noncomputable def terminalPrice (S r σ τ : ℝ) (z : ℝ) : ℝ :=
  S * Real.exp ((r - σ ^ 2 / 2) * τ + σ * Real.sqrt τ * z)

end BlackScholesModel


