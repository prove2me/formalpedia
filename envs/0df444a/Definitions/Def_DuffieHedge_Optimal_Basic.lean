-- Prove2me | Definitions.Def_DuffieHedge_Optimal_Basic
-- name    : DuffieHedge_Optimal_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:55:56.186243+00:00
-- url     : https://prove2.me/theorems/f34b5292-2eb0-45b0-b956-fdb9d7b0ec61
-- title:
--   The two-asset futures market (1), trading strategies, futures gains, problems (2)–(3), the tracking process (9) and the feedback SDE (10)–(11)
-- statement:
--   This file sets up the continuous-time hedging model of Duffie and Richardson.
--
--   **The market.** Fix a horizon $T>0$ and a probability space $(\Omega,\mathcal F,P)$ carrying a standard two-dimensional Brownian motion $(B,\varepsilon)$, with the filtration $\mathbb F$ it generates. Let $\mu,\sigma,m,v,\rho$ be measurable functions of time, bounded on $[0,T]$, with $|v_t|\ge\delta>0$ and $\rho_t\in[-1,1]$ for $t\in[0,T]$. Put $\xi_t=\int_0^t\rho_s\,dB_s+\int_0^t\sqrt{1-\rho_s^2}\,d\varepsilon_s$. The price $S$ of the committed asset and the futures price $F$ solve
--
--   $$dS_t=\mu_tS_t\,dt+\sigma_tS_t\,dB_t,\qquad dF_t=m_tF_t\,dt+v_tF_t\,d\xi_t,$$
--
--   with $S_0>0$, $F_0>0$. These are the **standing hypotheses**.
--
--   **Trading strategies and gains.** A **trading strategy** is a progressively measurable process $\theta$ with $E\int_0^T\theta_t^2F_t^2\,dt<\infty$; $\Theta$ is the set of them. The futures gain of $\theta$ is the Itô integral $G(\theta)_t=\int_0^t\theta_s\,dF_s$, and the terminal wealth of a hedger committed to $k$ units of $S$ at $T$ is $W(\theta)=kS_T+G(\theta)_T$.
--
--   **The problems.** Given a target $L\in\mathbb R$, a strategy $\varphi$ **solves problem (3)** if $\varphi\in\Theta$ and
--
--   $$E\big[(W(\varphi)-L)^2\big]\le E\big[(W(\theta)-L)^2\big]\quad\text{for every }\theta\in\Theta.$$
--
--   For $c\in\mathbb R$ and the quadratic utility $u(w)=w-cw^2$, $\varphi$ **solves problem (2)** if $\varphi\in\Theta$ and $E\,u(W(\theta))\le E\,u(W(\varphi))$ for every $\theta\in\Theta$. A strategy $\varphi$ is **mean-variance efficient** if $\varphi\in\Theta$ and no $\theta\in\Theta$ with $E\,W(\theta)=E\,W(\varphi)$ has $\operatorname{var}W(\theta)<\operatorname{var}W(\varphi)$.
--
--   **The optimal feedback strategy.** Let $\gamma_t=m_t\sigma_t\rho_t/v_t-\mu_t$ and define the **tracking process** (9)
--
--   $$Z_t=k\exp\Big(-\int_t^T\gamma_s\,ds\Big)S_t,$$
--
--   so $Z_T=kS_T$. The feedback map (11) is
--
--   $$\Phi_t(g)=\frac1{F_t}\Big[\frac{m_t}{v_t^2}(L-Z_t-g)-\frac{\sigma_t\rho_t}{v_t}Z_t\Big],$$
--
--   and a process $G^*$ **solves (10)**, $dG^*_t=\Phi(G^*_t)\,dF_t$, $G^*_0=0$, if the strategy $\varphi_t=\Phi_t(G^*_t)$ is a trading strategy and $G^*$ is its gain process.
--
--   These objects are shared by every statement of the mission: Proposition 1 asserts that $\Phi(G^*)$ solves problem (3).
--
--   **Formalization Note.** Stochastic integrals are those of the published definition `Peng1990_SMP_Stochastic` (the $L^2$ Itô integral, as a relation): `IsGain θ G` says $G$ is *a version* of $G(\theta)$, and every statement quantifies over all versions. $(B,\varepsilon)$ is one process with values in $\mathbb R^2$, $B$ = coordinate 0, $\varepsilon$ = coordinate 1; $d\xi$ is expanded as $\rho\,dB+\sqrt{1-\rho^2}\,d\varepsilon$, as the paper does on p. 5. Time is $\mathbb R_{\ge0}$; only values on $[0,T]$ matter, and the coefficients are taken measurable on all of $\mathbb R_{\ge0}$. The filtration is the natural filtration of $(B,\varepsilon)$, not its augmentation, and trading strategies are progressively measurable rather than predictable (the paper's §3.1 says "$\mathbb F$-predictable"): every progressive $\theta$ with $E\int\theta^2F^2<\infty$ agrees $dt\otimes dP$-a.e. with a predictable one with the same stochastic integral, so the set $\{G(\theta)_T:\theta\in\Theta\}$ and problem (3) are unchanged. The objective of (3) and the variance are lower integrals in $[0,\infty]$, so a non-square-integrable wealth gets $+\infty$, never a junk $0$. The paper's p. 2 says $\rho_t\in[0,1]$; §3.1, the rigorous formulation, allows $\rho_t\in[-1,1]$, which is used here. The factor $1/F_t$ is $0$ in Lean when $F_t=0$; $F$ is almost surely positive, so this value is never used. $T>0$ and $P(\Omega)=1$ are stated explicitly.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §2 (1)–(3) pp. 1–2, §3.1 pp. 3–4, §3.3 (9)–(11) pp. 4–5, §4.2 p. 6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

namespace DuffieHedge.Optimal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- §2 (1) and §3.1: the data of the two-asset futures market. `BE t ω 0` is the Brownian motion
`B` driving the committed asset, `BE t ω 1` is the independent Brownian motion `ε`; the futures
price is driven by `ξ = ∫ ρ dB + ∫ √(1 − ρ²) dε`. `μ, σ` are the drift and volatility of `S`,
`m, v` those of `F`, `ρ` the instantaneous correlation, `T` the horizon. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  T : ℝ≥0
  BE : ℝ≥0 → Ω → Fin 2 → ℝ
  hBE : Peng1990.SMP.IsStdBrownian P BE
  μ : ℝ≥0 → ℝ
  σ : ℝ≥0 → ℝ
  m : ℝ≥0 → ℝ
  v : ℝ≥0 → ℝ
  ρ : ℝ≥0 → ℝ
  S0 : ℝ
  F0 : ℝ
  S : ℝ≥0 → Ω → ℝ
  F : ℝ≥0 → Ω → ℝ

namespace Market

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : Market Ω)

/-- The filtration generated by `(B, ε)` (Peng's natural filtration of the Brownian motion). -/
noncomputable def filt : Filtration ℝ≥0 mΩ := Peng1990.SMP.brownianFiltration M.hBE

/-- The `dB`/`dε` loadings of `dξ`: `ρ_t` on `B` (coordinate 0) and `√(1 − ρ_t²)` on `ε`
(coordinate 1). -/
noncomputable def xiLoad (j : Fin 2) (t : ℝ≥0) : ℝ :=
  if j = 0 then M.ρ t else Real.sqrt (1 - M.ρ t ^ 2)

/-- §3.1 standing hypotheses: `P` is a probability measure, `T > 0`; `μ, σ, m, v, ρ` are
measurable and bounded on `[0, T]`, `v` is bounded away from zero and `ρ_t ∈ [−1, 1]`;
`S₀ > 0`, `F₀ > 0`; and the prices solve (1):
`dS = μS dt + σS dB`, `dF = mF dt + vF dξ = mF dt + vFρ dB + vF√(1 − ρ²) dε`. -/
def Standing : Prop :=
  IsProbabilityMeasure M.P ∧ 0 < M.T ∧
  Measurable M.μ ∧ Measurable M.σ ∧ Measurable M.m ∧ Measurable M.v ∧ Measurable M.ρ ∧
  (∃ K : ℝ, ∀ t ≤ M.T,
    |M.μ t| ≤ K ∧ |M.σ t| ≤ K ∧ |M.m t| ≤ K ∧ |M.v t| ≤ K ∧ |M.ρ t| ≤ K) ∧
  (∃ δ : ℝ, 0 < δ ∧ ∀ t ≤ M.T, δ ≤ |M.v t|) ∧
  (∀ t ≤ M.T, M.ρ t ∈ Set.Icc (-1 : ℝ) 1) ∧
  0 < M.S0 ∧ 0 < M.F0 ∧
  Peng1990.SMP.IsItoProcess M.filt M.P M.T M.BE (fun _ : Unit => M.S0)
    (fun s ω _ => M.μ s * M.S s ω)
    (fun j s ω _ => if j = 0 then M.σ s * M.S s ω else 0)
    (fun t ω _ => M.S t ω) ∧
  Peng1990.SMP.IsItoProcess M.filt M.P M.T M.BE (fun _ : Unit => M.F0)
    (fun s ω _ => M.m s * M.F s ω)
    (fun j s ω _ => M.v s * M.F s ω * M.xiLoad j s)
    (fun t ω _ => M.F t ω)

/-- §3.1: `θ ∈ Θ`, a trading strategy — `θ` is progressively measurable for the filtration of
`(B, ε)` and `E ∫₀ᵀ θ_t² F_t² dt < ∞` (a lower integral in `ℝ≥0∞`). -/
def IsTradingStrategy (θ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive M.filt θ ∧
  ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) M.T, ‖θ t.toNNReal ω * M.F t.toNNReal ω‖ₑ ^ 2 ∂volume ∂M.P < ⊤

/-- `G` is a version of the futures gain `G(θ)_t = ∫₀ᵗ θ_s dF_s` on `[0, T]`:
`dG = θmF dt + θvFρ dB + θvF√(1 − ρ²) dε`, `G₀ = 0`. -/
def IsGain (θ G : ℝ≥0 → Ω → ℝ) : Prop :=
  Peng1990.SMP.IsItoProcess M.filt M.P M.T M.BE (fun _ : Unit => 0)
    (fun s ω _ => θ s ω * M.m s * M.F s ω)
    (fun j s ω _ => θ s ω * M.v s * M.F s ω * M.xiLoad j s)
    (fun t ω _ => G t ω)

/-- Terminal wealth `W = k S_T + G_T` for a gain process `G`. -/
noncomputable def wealth (k : ℝ) (G : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  k * M.S M.T ω + G M.T ω

/-- The objective of problem (3), `E[(W − L)²]`, as a lower integral in `ℝ≥0∞`
(a wealth that is not square integrable has objective `+∞`). -/
noncomputable def objective (k L : ℝ) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ‖M.wealth k G ω - L‖ₑ ^ 2 ∂M.P

/-- `φ` solves problem (3): `φ` is a trading strategy, and for every version `Gφ` of `G(φ)`,
every trading strategy `θ` and every version `Gθ` of `G(θ)`,
`E[(W(φ) − L)²] ≤ E[(W(θ) − L)²]`. -/
def SolvesP3 (k L : ℝ) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsTradingStrategy φ ∧
  ∀ Gφ, M.IsGain φ Gφ → ∀ θ, M.IsTradingStrategy θ → ∀ Gθ, M.IsGain θ Gθ →
    M.objective k L Gφ ≤ M.objective k L Gθ

/-- §3.3: `γ_t = m_t σ_t ρ_t / v_t − μ_t`. -/
noncomputable def γ (t : ℝ≥0) : ℝ := M.m t * M.σ t * M.ρ t / M.v t - M.μ t

/-- (9): the tracking process `Z_t = k exp(−∫ₜᵀ γ_s ds) S_t`. -/
noncomputable def Z (k : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  k * Real.exp (-∫ s in (t : ℝ)..(M.T : ℝ), M.γ s.toNNReal) * M.S t ω

/-- (11): the feedback map
`Φ_t(g) = (1/F_t) [ (m_t/v_t²)(L − Z_t − g) − (σ_t ρ_t / v_t) Z_t ]`. -/
noncomputable def Φ (k L : ℝ) (t : ℝ≥0) (ω : Ω) (g : ℝ) : ℝ :=
  (1 / M.F t ω) *
    ((M.m t / M.v t ^ 2) * (L - M.Z k t ω - g) - (M.σ t * M.ρ t / M.v t) * M.Z k t ω)

/-- The feedback strategy `φ_t = Φ(G*_t)` generated by a process `G*`. -/
noncomputable def feedback (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.Φ k L t ω (Gs t ω)

/-- (10): `G*` solves `dG*_t = Φ(G*_t) dF_t`, `G*₀ = 0` — the strategy `Φ(G*)` is a trading
strategy and `G*` is a version of its futures gain. -/
def SolvesEq10 (k L : ℝ) (Gs : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsTradingStrategy (M.feedback k L Gs) ∧ M.IsGain (M.feedback k L Gs) Gs

/-- §4.2: mean of terminal wealth, `E[W]`. -/
noncomputable def meanW (k : ℝ) (G : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, M.wealth k G ω ∂M.P

/-- §4.2: variance of terminal wealth, `var[W]`, in `ℝ≥0∞`. -/
noncomputable def varW (k : ℝ) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  evariance (M.wealth k G) M.P

/-- §4.2: `φ` is mean-variance efficient — a trading strategy such that no trading strategy
`θ` with the same mean terminal wealth has a strictly smaller variance of terminal wealth. -/
def IsMVEfficient (k : ℝ) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsTradingStrategy φ ∧
  ∀ Gφ, M.IsGain φ Gφ → ∀ θ, M.IsTradingStrategy θ → ∀ Gθ, M.IsGain θ Gθ →
    M.meanW k Gθ = M.meanW k Gφ → M.varW k Gφ ≤ M.varW k Gθ

/-- §2, p. 2: the quadratic utility `u(w) = w − c w²`. -/
def quadUtility (c w : ℝ) : ℝ := w - c * w ^ 2

/-- §2 (2): `φ` solves problem (2), `max_{θ ∈ Θ} E(u[W(θ)])`. -/
def SolvesP2 (c k : ℝ) (φ : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsTradingStrategy φ ∧
  ∀ Gφ, M.IsGain φ Gφ → ∀ θ, M.IsTradingStrategy θ → ∀ Gθ, M.IsGain θ Gθ →
    ∫ ω, quadUtility c (M.wealth k Gθ ω) ∂M.P ≤ ∫ ω, quadUtility c (M.wealth k Gφ ω) ∂M.P

end Market

end DuffieHedge.Optimal


