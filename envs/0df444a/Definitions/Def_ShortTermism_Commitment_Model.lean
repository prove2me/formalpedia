-- Prove2me | Definitions.Def_ShortTermism_Commitment_Model
-- name    : ShortTermism_Commitment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:08.757824+00:00
-- url     : https://prove2.me/theorems/978bac7a-4c32-4872-b134-1f0eed2f87e4
-- title:
--   §2, §4.1–§4.3, A.2.1, A.4.3 — levered-firm HJB integrand (18), unlevered effort policy (25), no-overhang (A.27) and no-underinvestment (A.29) problems
-- statement:
--   This file sets up the dynamic-agency model of a levered firm of Hackbarth, Rivera and Wong (§2), in the reduced form in which the shareholders' problem becomes a boundary-value problem for the equity value $f(\delta)$ as a function of firm size $\delta$.
--
--   **Parameters.** The discount rate $r$, the baseline growth rate $\phi$ of firm size, the baseline profitability drift $\psi$, the volatilities $\sigma_\delta,\sigma_A$ of the permanent and transitory shocks with correlation $\rho$, the manager's coefficient of absolute risk aversion $\gamma$, the effort-cost coefficients $\theta_a,\theta_e,\theta_{ae}$, the corporate tax rate $\tau$, the effort bounds $\bar a,\bar e$ and the absorbing lower boundary $\underline\delta$ of firm size. The **standing assumptions** of §2 are
--   $$r>0,\quad \sigma_\delta>0,\quad \sigma_A>0,\quad \rho\in[-1,1],\quad \gamma>0,\quad \tau\in(0,1),\quad \bar a>0,\quad \bar e>0,\quad \underline\delta>0,$$
--   together with $\phi<r$, which the transversality limit $\psi/(r-\phi)$ presupposes. The coefficients $\theta_a,\theta_e,\theta_{ae},\psi,\phi$ carry no sign restriction.
--
--   **The HJB integrand.** For a coupon $C$, firm size $\delta$, long-term effort $a$, short-term effort $e$, and numbers $f_1,f_2$ standing for $f'(\delta)$ and $f''(\delta)$, the braces of the HJB equation (18) are
--   $$H_C(\delta,a,e,f_1,f_2)=\delta(\psi+e)-(1-\tau)C-\tfrac12(\theta_a a^2+2\theta_{ae}ae+\theta_e e^2)\delta+(\phi+a)\delta f_1+\tfrac12\sigma_\delta^2\delta^2 f_2-\frac{\gamma r\delta^2}{2}\,\Sigma(a,e),$$
--   $$\Sigma(a,e)=(\theta_a a+\theta_{ae}e)^2\sigma_\delta^2+(\theta_e e+\theta_{ae}a)^2\sigma_A^2+2\rho(\theta_a a+\theta_{ae}e)(\theta_e e+\theta_{ae}a)\sigma_\delta\sigma_A .$$
--   With $C=0$ this is the braces of the unlevered HJB (25). The condensed coefficients of Appendix A.2.1 are
--   $$\hat A=\theta_a+\gamma r\delta(\theta_a^2\sigma_\delta^2+\theta_{ae}^2\sigma_A^2+2\theta_{ae}\theta_a\sigma_\delta\sigma_A\rho),\qquad \hat D=\theta_e+\gamma r\delta(\theta_{ae}^2\sigma_\delta^2+\theta_e^2\sigma_A^2+2\theta_{ae}\theta_e\sigma_A\sigma_\delta\rho),$$
--   $$\hat B=\theta_{ae}+\gamma r\delta(\theta_a\theta_{ae}\sigma_\delta^2+\theta_e\theta_{ae}\sigma_A^2+(\theta_a\theta_e+\theta_{ae}^2)\sigma_\delta\sigma_A\rho),$$
--   and the condensed objective is $a f_1+e-a^2\hat A/2-e^2\hat D/2-ae\hat B$.
--
--   **Unlevered value and effort policy.** The predicate `IsUnleveredValue` requires $f_u(0)=0$, twice continuous differentiability on $(0,\infty)$, linear growth, and the unlevered HJB (25): $r f_u(\delta)$ is the attained maximum of $(a,e)\mapsto H_0(\delta,a,e,f_u'(\delta),f_u''(\delta))$ over the effort box for every $\delta>0$. Given this value, a pair of functions $(a_u,e_u)$ is an *unlevered effort policy* if for every $\delta\ge\underline\delta$ the pair $(a_u(\delta),e_u(\delta))$ lies in $[0,\bar a]\times[0,\bar e]$ and attains that maximum.
--
--   **Boundary conditions.** A function $f$ and a default threshold $\delta_B$ satisfy the boundary conditions if $\underline\delta\le\delta_B$, $f$ is twice continuously differentiable on $(\delta_B,\infty)$, $f(\delta_B)=0$ (value matching), the right derivative of $f$ at $\delta_B$ is $0$ (smooth pasting), and $f'(\delta)\to\psi/(r-\phi)$ as $\delta\to\infty$ (transversality).
--
--   **The two problems.** $(f,\delta_B)$ solves the **no-overhang problem (A.27)** if it satisfies the boundary conditions and
--   $$r f(\delta)=H_C\big(\delta,a_u(\delta),e_u(\delta),f'(\delta),f''(\delta)\big)\qquad\text{for all }\delta>\delta_B;$$
--   it solves the **no-underinvestment problem (A.29)** if it satisfies the boundary conditions and, for all $\delta>\delta_B$, the maximum of $e\mapsto H_C(\delta,a_u(\delta),e,f'(\delta),f''(\delta))$ over $e\in[0,\bar e]$ is attained and equals $r f(\delta)$.
--
--   These objects are shared by every statement of the mission: the no-overhang case fixes both efforts at the unlevered policy, the no-underinvestment case fixes only the long-term effort and lets the shareholders reoptimize short-term effort.
--
--   **Formalization Note** All quantities are real. $f'$ and $f''$ are Lean's `deriv f` and `deriv (deriv f)`, meaningful because $f$ is required to be $C^2$ on the open set $(\delta_B,\infty)$. The default threshold $\delta_B$ is a parameter (the page's "$\max_{\delta_B}$" is encoded by the smooth-pasting condition). A maximum is encoded as `IsGreatest` of the image, so attainment is part of the statement. The paper's "$\lim_{\delta\to\infty} f'(\delta)\to\psi/(r-\phi)$" is `Tendsto (deriv f) atTop (nhds (ψ/(r-φ)))`. The bankruptcy cost $\alpha$ does not enter these problems and is not a parameter.
-- source:
--   Hackbarth, Rivera & Wong, Optimal Short-Termism, ECGI Finance Working Paper 546/2018 (June 2021 version, SSRN 3060869), pp. 6–19 and 46–50 (PDF 10–23, 50–54): §2 (1)–(3) and effort cost, Definition 1, (18)–(19), (25)–(26), Proposition 3, §4.3 cases NO and NU, A.2.1, A.4.3 (A.27), (A.29)

import Mathlib

noncomputable section

namespace ShortTermism.Commitment

/-- The primitive parameters of §2 (pp. 6–8) that enter the HJB (18). -/
structure Params where
  /-- discount rate r -/
  r : ℝ
  /-- baseline growth rate φ of the firm size -/
  φ : ℝ
  /-- baseline drift ψ of the profitability -/
  ψ : ℝ
  /-- volatility σ_δ of the firm size -/
  σδ : ℝ
  /-- volatility σ_A of the profitability -/
  σA : ℝ
  /-- correlation ρ of the permanent and transitory shocks -/
  ρ : ℝ
  /-- coefficient γ of absolute risk aversion of the manager -/
  γ : ℝ
  /-- effort-cost coefficient θ_a -/
  θa : ℝ
  /-- effort-cost coefficient θ_e -/
  θe : ℝ
  /-- effort-cost interaction coefficient θ_ae -/
  θae : ℝ
  /-- corporate tax rate τ -/
  τ : ℝ
  /-- upper bound ā on long-term effort -/
  abar : ℝ
  /-- upper bound ē on short-term effort -/
  ebar : ℝ
  /-- absorbing lower boundary δ̲ of the firm size -/
  dlow : ℝ

/-- The standing assumptions of §2, plus φ < r (presupposed by ψ/(r − φ) in (A.27)–(A.29)). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.r ∧ P.φ < P.r ∧ 0 < P.σδ ∧ 0 < P.σA ∧ -1 ≤ P.ρ ∧ P.ρ ≤ 1 ∧ 0 < P.γ ∧
  0 < P.τ ∧ P.τ < 1 ∧ 0 < P.abar ∧ 0 < P.ebar ∧ 0 < P.dlow

/-- The bracket of the incentive cost in (18):
(θa a + θae e)²σδ² + (θe e + θae a)²σA² + 2ρ(θa a + θae e)(θe e + θae a)σδσA. -/
def incentiveSigma (P : Params) (a e : ℝ) : ℝ :=
  (P.θa * a + P.θae * e) ^ 2 * P.σδ ^ 2 + (P.θe * e + P.θae * a) ^ 2 * P.σA ^ 2
    + 2 * P.ρ * (P.θa * a + P.θae * e) * (P.θe * e + P.θae * a) * P.σδ * P.σA

/-- The braces of (18) for coupon `C`, at firm size `δ` and effort `(a, e)`, with `f1 = f′(δ)` and
`f2 = f″(δ)`. With `C = 0` these are the braces of (25); at `(a, e) = (a_u(δ), e_u(δ))` those of
(A.27); at `a = a_u(δ)` those of (A.29). -/
def hjbIntegrand (P : Params) (C δ a e f1 f2 : ℝ) : ℝ :=
  δ * (P.ψ + e) - (1 - P.τ) * C - (P.θa * a ^ 2 + 2 * P.θae * a * e + P.θe * e ^ 2) * δ / 2
    + (P.φ + a) * δ * f1 + 1 / 2 * P.σδ ^ 2 * δ ^ 2 * f2
    - P.γ * P.r * δ ^ 2 / 2 * incentiveSigma P a e

/-- The effort box `[0, ā] × [0, ē]` of Definition 1 and A.2.1. -/
def effortBox (P : Params) : Set (ℝ × ℝ) := Set.Icc 0 P.abar ×ˢ Set.Icc 0 P.ebar

/-- Â of A.2.1. -/
def Ahat (P : Params) (δ : ℝ) : ℝ :=
  P.θa + P.γ * P.r * δ *
    (P.θa ^ 2 * P.σδ ^ 2 + P.θae ^ 2 * P.σA ^ 2 + 2 * P.θae * P.θa * P.σδ * P.σA * P.ρ)

/-- D̂ of A.2.1. -/
def Dhat (P : Params) (δ : ℝ) : ℝ :=
  P.θe + P.γ * P.r * δ *
    (P.θae ^ 2 * P.σδ ^ 2 + P.θe ^ 2 * P.σA ^ 2 + 2 * P.θae * P.θe * P.σA * P.σδ * P.ρ)

/-- B̂ of A.2.1. -/
def Bhat (P : Params) (δ : ℝ) : ℝ :=
  P.θae + P.γ * P.r * δ * (P.θa * P.θae * P.σδ ^ 2 + P.θe * P.θae * P.σA ^ 2
    + (P.θa * P.θe + P.θae ^ 2) * P.σδ * P.σA * P.ρ)

/-- The condensed objective of A.2.1 and A.4.2: `a f′ + e − a²Â/2 − e²D̂/2 − a e B̂`. -/
def condensedObj (P : Params) (δ a e f1 : ℝ) : ℝ :=
  a * f1 + e - a ^ 2 * Ahat P δ / 2 - e ^ 2 * Dhat P δ / 2 - a * e * Bhat P δ

/-- The unlevered firm value of §4.2 and Proposition 3: a C² solution with linear growth
of the unlevered HJB (25), with the boundary value `fu(0) = 0`. -/
def IsUnleveredValue (P : Params) (fu : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 fu (Set.Ioi 0) ∧ fu 0 = 0 ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 ≤ δ → |fu δ| ≤ K * (1 + δ)) ∧
    ∀ δ : ℝ, 0 < δ → IsGreatest
      ((fun p => hjbIntegrand P 0 δ p.1 p.2 (deriv fu δ) (deriv (deriv fu) δ)) '' effortBox P)
      (P.r * fu δ)

/-- `(au, eu)` is an unlevered effort policy for `fu`: for every `δ ≥ δ̲` the pair
`(au δ, eu δ)` lies in the effort box and maximizes the braces of (25) (coupon 0) at
`fu′(δ), fu″(δ)` over the box. -/
def IsUnleveredPolicy (P : Params) (fu au eu : ℝ → ℝ) : Prop :=
  ∀ δ, P.dlow ≤ δ → (au δ, eu δ) ∈ effortBox P ∧
    ∀ p ∈ effortBox P, hjbIntegrand P 0 δ p.1 p.2 (deriv fu δ) (deriv (deriv fu) δ)
      ≤ hjbIntegrand P 0 δ (au δ) (eu δ) (deriv fu δ) (deriv (deriv fu) δ)

/-- Value matching, smooth pasting and transversality, common to (A.27) and (A.29), together with
the regularity under which `f′` and `f″` are meant: `δ̲ ≤ δ_B`, `f` is C² on `(δ_B, ∞)`,
`f(δ_B) = 0`, the right derivative of `f` at `δ_B` is `0`, and `f′(δ) → ψ/(r − φ)` as `δ → ∞`. -/
def BoundaryConds (P : Params) (f : ℝ → ℝ) (dB : ℝ) : Prop :=
  P.dlow ≤ dB ∧ ContDiffOn ℝ 2 f (Set.Ioi dB) ∧ f dB = 0 ∧
  HasDerivWithinAt f 0 (Set.Ici dB) dB ∧
  Filter.Tendsto (deriv f) Filter.atTop (nhds (P.ψ / (P.r - P.φ)))

/-- `(f, δ_B)` solves the no-overhang problem (A.27): both efforts fixed at `(au, eu)`. -/
def SolvesNO (P : Params) (C : ℝ) (au eu f : ℝ → ℝ) (dB : ℝ) : Prop :=
  BoundaryConds P f dB ∧
  ∀ δ, dB < δ → P.r * f δ = hjbIntegrand P C δ (au δ) (eu δ) (deriv f δ) (deriv (deriv f) δ)

/-- `(f, δ_B)` solves the no-underinvestment problem (A.29): long-term effort fixed at `au`,
short-term effort maximized over `[0, ē]`. -/
def SolvesNU (P : Params) (C : ℝ) (au f : ℝ → ℝ) (dB : ℝ) : Prop :=
  BoundaryConds P f dB ∧
  ∀ δ, dB < δ → IsGreatest
    ((fun e => hjbIntegrand P C δ (au δ) e (deriv f δ) (deriv (deriv f) δ)) '' Set.Icc 0 P.ebar)
    (P.r * f δ)

end ShortTermism.Commitment

end


