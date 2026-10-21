-- Prove2me | Definitions.Def_DynMomentum_ShortHorizon_Model
-- name    : DynMomentum_ShortHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:48.025984+00:00
-- url     : https://prove2.me/theorems/de034882-8f72-40ce-af97-7bd0ecde950e
-- title:
--   §2.1, (3.3), (3.8), (A.9), (A.11), (A.14), pp. 5–28 — momentum model parameters, the ODE system (A.9), the weights ω̂, ω, C₀, C₁ and the weights φ*, φᴹ, φᴴ
-- statement:
--   This file sets up the objects of Li and Liu's optimal dynamic momentum model for an investment horizon no longer than the look-back period.
--
--   **Model.** A risky asset has price $S_t$ with $dS_t/S_t = [\alpha m_t + (1-\alpha)\mu + r]\,dt + \sigma\,dB_t$, where the momentum $m_t = \frac1\tau\int_{t-\tau}^t (dS_u/S_u - r\,du)$ is the moving average of excess returns over a look-back window of length $\tau$. The parameters are bundled as $(\alpha,\sigma,\tau,\gamma,r,\mu)$, with **standing assumptions** $0<\alpha<1$, $\sigma>0$, $\tau>0$ and a CRRA coefficient $\gamma>0$; $r$ and $\mu$ are arbitrary reals. Time is normalized so that the investor stands at $t=0$, the horizon is $T$, and $s:\mathbb R\to\mathbb R$ is the realized log-price path, $s_v=\ln S_v$, observed on $[-\tau,0]$.
--
--   **Riccati denominator.** With $E_{T}(u) = e^{2\alpha(T-u)/(\sqrt\gamma\,\tau)}$,
--   $$D(T,u) = (\sqrt\gamma-1)\,E_T(u) + (\sqrt\gamma+1).$$
--
--   **The ODE system (A.9).** The three right-hand sides are, at ODE time $u$ with forcing $s_{u-\tau}$,
--   $$\dot A_1 = -\sigma^2A_1^2 - \tfrac{2\alpha}{\gamma\tau}A_1 - \tfrac{1-\gamma}{\gamma^2}\tfrac{\alpha^2}{\tau^2\sigma^2},$$
--   $$\dot A_2 = -\big(\sigma^2A_1+\tfrac{\alpha}{\gamma\tau}\big)A_2 - \Big[(1-\alpha)\tfrac{\mu}{\gamma} + \big(r-\tfrac{\sigma^2}2\big)\big(1-\tfrac\alpha\gamma\big) - \tfrac{\alpha}{\gamma\tau}s_{u-\tau}\Big]A_1 - \tfrac{1-\gamma}{\gamma^2}\tfrac{\alpha}{\sigma^2\tau}\Big[(1-\alpha)\mu+\alpha\big(\tfrac{\sigma^2}2-r\big)-\tfrac\alpha\tau s_{u-\tau}\Big],$$
--   $$\dot A_3 = -\tfrac{\sigma^2}2A_2^2 - \tfrac{\sigma^2}2A_1 - [\,\cdots\,]A_2 - \tfrac{1-\gamma}{2\gamma^2\sigma^2}\Big[(1-\alpha)\mu+\alpha\big(\tfrac{\sigma^2}2-r\big)-\tfrac\alpha\tau s_{u-\tau}\Big]^2,$$
--   with the same bracket $[\cdots]$ as in $\dot A_2$. A pair $(A_1,A_2)$ *solves (A.9)* if the first two equations hold on $[0,T]$ (derivatives taken within $[0,T]$) and $A_1(T)=A_2(T)=0$; the full version adds $A_3$ with $A_3(T)=0$. Also defined are the drift and the potential of the Feynman–Kac PDE (A.8) and the ansatz $f(x,t)=\exp\{A_{1,t}x^2/2+A_{2,t}x+A_{3,t}\}$.
--
--   **Weights.** The market price of risk at time $0$, (3.3) with (2.3), is
--   $$\theta_0 = \frac{(1-\alpha)\mu - \alpha(r-\sigma^2/2) + \frac\alpha\tau(s_0-s_{-\tau})}{\sigma},$$
--   and the optimal weight (A.11) is $\phi^*_0 = \theta_0/(\gamma\sigma) + A_{1,0}s_0 + A_{2,0}$. From (A.14):
--   $$C_{0,u} = \frac{\alpha^2(E_T(u)+1)}{\gamma^{3/2}\sigma^2\tau^2 D(T,u)},\qquad \hat\omega_u = \frac{\gamma\sigma^2}{\alpha}C_{0,u+\tau}\exp\Big\{\int_0^{u+\tau}\Big[\frac{\gamma(1-\gamma)\sigma^2\tau}{\alpha}C_{0,\hat u}+\frac\alpha\tau\Big]d\hat u\Big\},$$
--   $\omega_v = \int_{-\tau}^{\min(v,\,T-\tau)}\hat\omega_u\,du$ (which is both printed branches), and the constant
--   $$C_1 = \int_0^T e^{\int_0^u[\frac{\gamma(1-\gamma)\sigma^2\tau}{\alpha}C_{0,\hat u}+\frac\alpha\tau]d\hat u}\Big\{\Big[\frac{(1-\alpha)\mu-\alpha r}{\gamma}+r\Big]\frac{\gamma(1-\gamma)\tau}{\alpha}C_{0,u} + r\frac{(\gamma-1)\alpha}{\gamma\sigma^2\tau}\Big\}du + (1-\gamma)r\frac{\alpha}{\gamma\sigma^2}\int_{-\tau}^0\omega_v\,dv.$$
--   Finally, the weighted excess return $\int_{-\tau}^0 w_v(dS_v/S_v - r\,dv)$ of a deterministic absolutely continuous weight $w$ with derivative $w'$ is read pathwise as
--   $$w_0s_0 - w_{-\tau}s_{-\tau} - \int_{-\tau}^0 w'_vs_v\,dv + \Big(\frac{\sigma^2}2-r\Big)\int_{-\tau}^0 w_v\,dv,$$
--   and the two components of (3.8) are $\phi^M_0 = \frac{\alpha}{\gamma\sigma^2}\int_{-\tau}^0\frac1\tau(dS_v/S_v-r\,dv)+\frac{(1-\alpha)\mu}{\gamma\sigma^2}$ and $\phi^H_0 = \frac{(1-\gamma)\alpha}{\gamma\sigma^2}\int_{-\tau}^0\omega_v(dS_v/S_v-r\,dv)+C_1$, with $\omega' = \hat\omega$ on $[-\tau,T-\tau]$ and $0$ after.
--
--   These objects are the whole vocabulary of Proposition 3.3 and its proof in Appendix A.2.
--
--   **Formalization Note.** (1) $C_1$ is the printed (A.14) formula with both occurrences of $-\sigma^2/2$ deleted (after "$+r$" in the first bracket and inside $(r-\sigma^2/2)$ of the second term); the printed constant makes (3.8) false by a path-independent amount, while the corrected one gives $C_1=0$ at $\gamma=1$. (2) The pathwise reading of $\int w(dS/S - r\,dv)$ combines Itô's formula $dS/S = ds + \frac{\sigma^2}2dv$ with the product rule; it is not on the page. (3) $\gamma^{3/2}$ is written $\gamma\sqrt\gamma$. (4) The stochastic layer of the paper is not formalized: $\phi^*_0$ is *defined* by (A.11).
-- source:
--   Li & Liu, Optimal Dynamic Momentum Strategies, Operations Research (2022), DOI 10.1287/opre.2021.2254, author manuscript pp. 5–10, 26–28 (PDF 5–10, 26–28), (2.1)–(2.3), (3.3), (3.8), (A.8), (A.9), (A.11), (A.14)

import Mathlib

namespace DynMomentum.ShortHorizon

/-- Parameters of the momentum model (2.1)–(2.3) and the CRRA investor (3.1) of Li & Liu (2022):
momentum level `α`, volatility `σ`, look-back length `τ`, relative risk aversion `γ`, short rate `r`
and unconditional risk premium `μ`. -/
structure Params where
  α : ℝ
  σ : ℝ
  τ : ℝ
  γ : ℝ
  r : ℝ
  μ : ℝ

namespace Params

/-- Standing assumptions: `0 < α < 1` (p. 6), `σ > 0`, `τ > 0`, CRRA coefficient `γ > 0` (p. 8). -/
def Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 ∧ 0 < P.σ ∧ 0 < P.τ ∧ 0 < P.γ

/-- The exponential `e^{2α(T-u)/(√γ τ)}` of (A.13)–(A.14). -/
noncomputable def expo (P : Params) (T u : ℝ) : ℝ :=
  Real.exp (2 * P.α * (T - u) / (Real.sqrt P.γ * P.τ))

/-- The Riccati denominator `(√γ - 1) e^{2α(T-u)/(√γ τ)} + (√γ + 1)` of (A.13)–(A.14). -/
noncomputable def D (P : Params) (T u : ℝ) : ℝ :=
  (Real.sqrt P.γ - 1) * P.expo T u + (Real.sqrt P.γ + 1)

end Params

/-- Right-hand side of the first ODE of (A.9) (the Riccati equation for `A₁`). -/
noncomputable def rhs1 (P : Params) (a1 : ℝ) : ℝ :=
  -P.σ ^ 2 * a1 ^ 2 - 2 * P.α / (P.γ * P.τ) * a1
    - (1 - P.γ) / P.γ ^ 2 * (P.α ^ 2 / (P.τ ^ 2 * P.σ ^ 2))

/-- Right-hand side of the second ODE of (A.9) at ODE time `u`, forced by the realized past log
price `s (u - τ)`. -/
noncomputable def rhs2 (P : Params) (s : ℝ → ℝ) (u a1 a2 : ℝ) : ℝ :=
  -(P.σ ^ 2 * a1 + P.α / (P.γ * P.τ)) * a2
    - ((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ)
        - P.α / (P.γ * P.τ) * s (u - P.τ)) * a1
    - (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
        * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r) - P.α / P.τ * s (u - P.τ))

/-- Right-hand side of the third ODE of (A.9) at ODE time `u`. -/
noncomputable def rhs3 (P : Params) (s : ℝ → ℝ) (u a1 a2 : ℝ) : ℝ :=
  -(P.σ ^ 2 / 2) * a2 ^ 2 - (P.σ ^ 2 / 2) * a1
    - ((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ)
        - P.α / (P.γ * P.τ) * s (u - P.τ)) * a2
    - (1 - P.γ) / (2 * P.γ ^ 2 * P.σ ^ 2)
        * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r) - P.α / P.τ * s (u - P.τ)) ^ 2

/-- `(A₁, A₂)` solves the first two ODEs of (A.9) on `[0, T]` with `A₁(T) = A₂(T) = 0`. -/
def SolvesA9 (P : Params) (T : ℝ) (s : ℝ → ℝ) (A1 A2 : ℝ → ℝ) : Prop :=
  (∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A1 (rhs1 P (A1 u)) (Set.Icc 0 T) u) ∧
  (∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A2 (rhs2 P s u (A1 u) (A2 u)) (Set.Icc 0 T) u) ∧
  A1 T = 0 ∧ A2 T = 0

/-- `(A₁, A₂, A₃)` solves the full system (A.9) on `[0, T]` with `A₁(T) = A₂(T) = A₃(T) = 0`. -/
def SolvesA9Full (P : Params) (T : ℝ) (s : ℝ → ℝ) (A1 A2 A3 : ℝ → ℝ) : Prop :=
  SolvesA9 P T s A1 A2 ∧
  (∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A3 (rhs3 P s u (A1 u) (A2 u)) (Set.Icc 0 T) u) ∧
  A3 T = 0

/-- Drift coefficient of `∂f/∂s` in the Feynman–Kac PDE (A.8), at time `t` and state `x`. -/
noncomputable def pdeDrift (P : Params) (s : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ) + (1 - P.α) * P.μ / P.γ
    + P.α / (P.γ * P.τ) * (x - s (t - P.τ))

/-- Potential (coefficient of `f`) in the Feynman–Kac PDE (A.8), at time `t` and state `x`. -/
noncomputable def pdePotential (P : Params) (s : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1 - P.γ) / (2 * P.γ ^ 2 * P.σ ^ 2)
    * ((1 - P.α) * P.μ - P.α * (P.r - P.σ ^ 2 / 2) + P.α / P.τ * (x - s (t - P.τ))) ^ 2

/-- The exponential-quadratic ansatz `f(x, t) = exp{A₁,ₜ x²/2 + A₂,ₜ x + A₃,ₜ}` of (A.9). -/
noncomputable def ansatz (A1 A2 A3 : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Real.exp (A1 t * x ^ 2 / 2 + A2 t * x + A3 t)

/-- Market price of risk at time 0, (3.3) with (2.3):
`θ₀ = [(1 - α)μ - α(r - σ²/2) + (α/τ)(s₀ - s₋τ)]/σ`, with `s` the log-price path. -/
noncomputable def theta0 (P : Params) (s : ℝ → ℝ) : ℝ :=
  ((1 - P.α) * P.μ - P.α * (P.r - P.σ ^ 2 / 2) + P.α / P.τ * (s 0 - s (-P.τ))) / P.σ

/-- The optimal weight at time 0, (A.11): `φ*₀ = θ₀/(γσ) + A₁,₀ s₀ + A₂,₀`. -/
noncomputable def phiStar (P : Params) (s : ℝ → ℝ) (A1 A2 : ℝ → ℝ) : ℝ :=
  theta0 P s / (P.γ * P.σ) + A1 0 * s 0 + A2 0

/-- `C₀,ᵤ = α²(e^{2α(T-u)/(√γ τ)} + 1) / (γ^{3/2} σ² τ² [(√γ - 1)e^{2α(T-u)/(√γ τ)} + (√γ + 1)])`,
(A.14). -/
noncomputable def C0 (P : Params) (T u : ℝ) : ℝ :=
  P.α ^ 2 * (P.expo T u + 1)
    / (P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T u)

/-- `ω̂ᵤ = (γσ²/α) C₀,ᵤ₊τ exp{∫₀^{u+τ} [(γ(1-γ)σ²τ/α) C₀,û + α/τ] dû}`, (A.14). -/
noncomputable def omegaHat (P : Params) (T u : ℝ) : ℝ :=
  P.γ * P.σ ^ 2 / P.α * C0 P T (u + P.τ)
    * Real.exp (∫ w in (0 : ℝ)..(u + P.τ),
        (P.γ * (1 - P.γ) * P.σ ^ 2 * P.τ / P.α * C0 P T w + P.α / P.τ))

/-- `ωᵥ = ∫_{-τ}^{v} ω̂ᵤ du` for `v ∈ [-τ, -τ + T]` and `ωᵥ = ∫_{-τ}^{-τ+T} ω̂ᵤ du` for
`v ∈ [-τ + T, 0]`, (A.14), written as one integral up to `min v (T - τ)`. -/
noncomputable def omega (P : Params) (T v : ℝ) : ℝ :=
  ∫ u in (-P.τ)..(min v (T - P.τ)), omegaHat P T u

/-- The constant `C₁` of (A.14), **corrected**: the printed formula carries `- σ²/2` in two places
(after `+ r` in the first bracket and in `(r - σ²/2)` of the second term); both are deleted here.
With the printed version the identity (3.8) fails by a path-independent constant (see the
mission's moderation notes); the corrected one gives `C₁ = 0` at `γ = 1`. -/
noncomputable def C1 (P : Params) (T : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..T,
      Real.exp (∫ w in (0 : ℝ)..u,
          (P.γ * (1 - P.γ) * P.σ ^ 2 * P.τ / P.α * C0 P T w + P.α / P.τ))
        * ((((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r)
              * (P.γ * (1 - P.γ) * P.τ / P.α) * C0 P T u
            + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ))))
    + (1 - P.γ) * P.r * (P.α / (P.γ * P.σ ^ 2)) * ∫ v in (-P.τ)..0, omega P T v

/-- Pathwise value of the weighted excess return `∫_{-τ}^{0} w_v (dS_v/S_v - r dv)` along a
log-price path `s` (`s_v = ln S_v`), for a deterministic absolutely continuous weight `w` with
derivative `w'`: Itô's formula `dS/S = ds + (σ²/2) dv` and the product rule
`d(w s) = w' s dv + w ds` give
`w₀ s₀ - w₋τ s₋τ - ∫_{-τ}^{0} w'_v s_v dv + (σ²/2 - r) ∫_{-τ}^{0} w_v dv`. -/
noncomputable def pathReturn (P : Params) (w w' : ℝ → ℝ) (s : ℝ → ℝ) : ℝ :=
  w 0 * s 0 - w (-P.τ) * s (-P.τ) - (∫ v in (-P.τ)..0, w' v * s v)
    + (P.σ ^ 2 / 2 - P.r) * ∫ v in (-P.τ)..0, w v

/-- Mean-variance component of (3.8):
`φᴹ₀ = (α/(γσ²)) ∫_{-τ}^{0} (1/τ)(dS_v/S_v - r dv) + (1 - α)μ/(γσ²)`. -/
noncomputable def phiM (P : Params) (s : ℝ → ℝ) : ℝ :=
  P.α / (P.γ * P.σ ^ 2) * pathReturn P (fun _ => 1 / P.τ) (fun _ => 0) s
    + (1 - P.α) * P.μ / (P.γ * P.σ ^ 2)

/-- Hedging component of (3.8):
`φᴴ₀ = ((1 - γ)α/(γσ²)) ∫_{-τ}^{0} ω_v (dS_v/S_v - r dv) + C₁`, with `ω' = ω̂` on `[-τ, T - τ]`
and `0` after. -/
noncomputable def phiH (P : Params) (T : ℝ) (s : ℝ → ℝ) : ℝ :=
  (1 - P.γ) * P.α / (P.γ * P.σ ^ 2)
      * pathReturn P (omega P T) (Set.indicator (Set.Icc (-P.τ) (T - P.τ)) (omegaHat P T)) s
    + C1 P T

end DynMomentum.ShortHorizon


