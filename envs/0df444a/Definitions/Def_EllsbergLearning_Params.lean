-- Prove2me | Definitions.Def_EllsbergLearning_Params
-- name    : EllsbergLearning_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:16.842665+00:00
-- url     : https://prove2.me/theorems/9c91d636-7f8b-4588-aacf-3f552ef4f58c
-- title:
--   The learning problem's data: parameters, priors, payoffs, posteriors $\underline m_t,\overline m_t$, payoff $X$ of (16), $\hat c$, $\overline f,\underline f$, indifference point, drift (46)
-- statement:
--   The data of the learning problem are two parameter values $\theta_0<\theta_1$, the signal volatility $\sigma>0$ of $Z_t=\theta t+\sigma B_t$, a per-unit-time learning cost $c>0$, the prior interval $[\underline m_0,\overline m_0]$ for the probability of $\theta_1$, with $0<\underline m_0<\overline m_0<1$, so that the set of priors is $\mathcal M_0=\{\mu^m=(1-m)\delta_{\theta_0}+m\delta_{\theta_1}:\underline m_0\le m\le\overline m_0\}$, payoffs $u_{ij}=u(a_i,\theta_j)\ge0$ for $i,j\in\{0,1\}$ and $u_2=u(a_2,\theta_0)=u(a_2,\theta_1)\ge0$. The standing assumptions are (14), $u_{00}=u_{11}>u_{01}$ and $u_{11}>u_{10}$, and $u_2<u_{00},u_{11}$. **Payoff symmetry** is $u_{01}=u_{10}$.
--
--   From these data:
--
--   1. the likelihood ratio $\varphi(t,z)=\exp\{\frac{\theta_1-\theta_0}{\sigma^2}z-\frac{1}{2\sigma^2}(\theta_1^2-\theta_0^2)t\}$ (13);
--   2. the posterior probability of $\theta_1$ from the prior $\mu^m$ after $Z_t=z$, $\frac{\frac{m}{1-m}\varphi(t,z)}{1+\frac{m}{1-m}\varphi(t,z)}$, and in particular $\underline m_t(z)$, $\overline m_t(z)$ (12) for $m=\underline m_0,\overline m_0$; the posterior mean $\hat\theta^{\mu^m}_t(z)$;
--   3. the Gilboa–Schmeidler utility $\min_{\mu\in\mathcal M_t}\int u(a_i,\theta)\,d\mu$ of $a_i$, the minimum of $(1-m)u_{i0}+m u_{i1}$ over $m\in[\underline m_t(z),\overline m_t(z)]$, and the payoff (16)
--   $$X(t,z)=\max\Big\{\min_{\mu\in\mathcal M_t}\int u(a_0,\theta)d\mu,\ \min_{\mu\in\mathcal M_t}\int u(a_1,\theta)d\mu,\ u_2\Big\};$$
--   4. the normalized cost $\hat c=2c\sigma^2/(\theta_1-\theta_0)^2$ and the boundary maps $\overline f(t,r)=\frac{\theta_1+\theta_0}{2}t+\frac{\sigma^2}{\theta_1-\theta_0}\log\big(\frac{1-\overline m_0}{\overline m_0}\frac{r}{1-r}\big)$ and $\underline f(t,r)$ (same with $\underline m_0$);
--   5. an **indifference point** $(\underline\pi,\overline\pi,\tilde z)$: $\underline\pi=\underline m_t(\tilde z_t)$, $\overline\pi=\overline m_t(\tilde z_t)$ for every $t$, and $\underline\pi u_{11}+(1-\underline\pi)u_{10}=\overline\pi u_{01}+(1-\overline\pi)u_{00}$;
--   6. the drift (46) of the signal under the worst-case prior: $\hat\theta^{\mu}_t(z)$ with $\mu=\mu^{\overline m_0}$ if $z<\tilde z_t$ and with $\mu=\mu^{\underline m_0}$ if $z\ge\tilde z_t$.
--
--   These are the deterministic objects every statement of the paper is built from.
--
--   **Formalization Note** Payoffs are indexed `u i j` with `i j : Fin 2`. The Gilboa–Schmeidler utility is written as the infimum of the image of the posterior interval, as printed; the interval is nonempty and compact. Deterministic functions take a real time $t$; the indifference trajectory is a function on $\mathbb R$, and the paper's trajectory is its restriction to $t\ge0$. The drift (46) is named `drift` because the paper also uses $f$ for $\overline f,\underline f$.
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §3.1, (10)–(16), pp.10–11; §4, p.19 (indifference point, ĉ), p.21 (f̄, f̲); Lemma 5.1, (46), p.26

import Mathlib

open Set

noncomputable section

namespace EllsbergLearning

/-- The scalar data of the learning problem of Epstein & Ji, *Optimal Learning under Robustness
and Time-Consistency*, arXiv:1708.01890v2, §3.1, pp.10–11: the two parameter values
`θ₀ < θ₁` (support of every prior, (10)), the signal volatility `σ` of `Z_t = θt + σB_t` ((6),
p.8), the per-unit-time learning cost `c`, the prior probability interval `[m̲₀, m̄₀]`
(`mLo0`, `mUp0`) of `θ₁` ((10)), the payoffs `u i j = u(aᵢ, θⱼ)` for `i, j ∈ {0, 1}` (p.11 and
the notation `u_ij` of §4, p.19), and the payoff `u₂ = u(a₂, θ₀) = u(a₂, θ₁)` of the third
action ((15)). -/
structure Params where
  θ₀ : ℝ
  θ₁ : ℝ
  σ : ℝ
  c : ℝ
  mLo0 : ℝ
  mUp0 : ℝ
  u : Fin 2 → Fin 2 → ℝ
  u₂ : ℝ

namespace Params

variable (p : Params)

/-- The standing assumptions of §3.1 (arXiv:1708.01890v2, pp.10–11): `θ₀ < θ₁`; `σ > 0`;
`c > 0`; `0 < m̲₀ < m̄₀ < 1`; every payoff `u(aᵢ, θⱼ)` nonnegative (including `u₂`);
(14): `u(aⱼ, θⱼ) = u(aᵢ, θᵢ) > u(aⱼ, θᵢ)` for `i ≠ j`, i.e. `u₀₀ = u₁₁`, `u₀₀ > u₀₁`,
`u₁₁ > u₁₀`; and `u₂ < u(aᵢ, θᵢ)` for `i = 0, 1`. -/
structure Valid : Prop where
  θ_lt : p.θ₀ < p.θ₁
  σ_pos : 0 < p.σ
  c_pos : 0 < p.c
  mLo0_pos : 0 < p.mLo0
  mLo0_lt_mUp0 : p.mLo0 < p.mUp0
  mUp0_lt_one : p.mUp0 < 1
  u_nonneg : ∀ i j, 0 ≤ p.u i j
  u₂_nonneg : 0 ≤ p.u₂
  u00_eq_u11 : p.u 0 0 = p.u 1 1
  u01_lt_u00 : p.u 0 1 < p.u 0 0
  u10_lt_u11 : p.u 1 0 < p.u 1 1
  u₂_lt_u00 : p.u₂ < p.u 0 0
  u₂_lt_u11 : p.u₂ < p.u 1 1

/-- Payoff symmetry `u(a₀, θ₁) = u(a₁, θ₀)`, i.e. `u₀₁ = u₁₀` (arXiv:1708.01890v2, p.11). -/
def PayoffSymmetry : Prop := p.u 0 1 = p.u 1 0

/-- The likelihood ratio (13), arXiv:1708.01890v2, p.11:
`ϕ(t, z) = exp{(θ₁ − θ₀)/σ² · z − (θ₁² − θ₀²) t/(2σ²)}`. -/
def phi (t z : ℝ) : ℝ :=
  Real.exp ((p.θ₁ - p.θ₀) / p.σ ^ 2 * z - (p.θ₁ ^ 2 - p.θ₀ ^ 2) * t / (2 * p.σ ^ 2))

/-- The posterior probability of `θ₁` at time `t` after the signal `Z_t = z`, from the prior
`µ^m = (1 − m)δ_{θ₀} + mδ_{θ₁}` ((10)–(12), arXiv:1708.01890v2, pp.10–11):
`(m/(1−m))ϕ(t,z) / (1 + (m/(1−m))ϕ(t,z))`.

**Formalization Note.** The posterior is given by its closed form (12), which the paper takes
from Liptser and Shiryaev (1977, Theorem 9.1). -/
def post (m t z : ℝ) : ℝ :=
  m / (1 - m) * p.phi t z / (1 + m / (1 - m) * p.phi t z)

/-- `m̲_t(z)`, the lower posterior probability of `θ₁` ((12), p.11). -/
def mLo (t z : ℝ) : ℝ := p.post p.mLo0 t z

/-- `m̄_t(z)`, the upper posterior probability of `θ₁` ((12), p.11). -/
def mUp (t z : ℝ) : ℝ := p.post p.mUp0 t z

/-- The posterior estimate `θ̂^µ_t = ∫ θ dµ_t` of the prior `µ^m` after `Z_t = z` (§2, p.8, and
§5.1, p.25): `(1 − post)θ₀ + post·θ₁`. It equals `θ₁ − (θ₁ − θ₀)/(1 + (m/(1−m))ϕ(t, z))`, the
expression appearing in (46) and on p.27. -/
def thetaHat (m t z : ℝ) : ℝ := (1 - p.post m t z) * p.θ₀ + p.post m t z * p.θ₁

/-- The Gilboa–Schmeidler utility `min_{µ ∈ M_t} ∫ u(aᵢ, θ) dµ` of action `aᵢ` (`i = 0, 1`) at
time `t` after the signal `z` (arXiv:1708.01890v2, p.11): the infimum of
`(1 − m)u(aᵢ, θ₀) + m u(aᵢ, θ₁)` over the posterior interval `m ∈ [m̲_t(z), m̄_t(z)]` of (11).

**Formalization Note.** Written as the infimum of the image of the interval, as printed; the
interval is nonempty and compact, so the infimum is a minimum (the closed form is milestone
`gs_closed_form`). -/
def gs (i : Fin 2) (t z : ℝ) : ℝ :=
  sInf ((fun m => (1 - m) * p.u i 0 + m * p.u i 1) '' Icc (p.mLo t z) (p.mUp t z))

/-- The payoff (16), arXiv:1708.01890v2, p.11: `X(t, z) = max{GS utility of a₀, GS utility of
a₁, u₂}`, the indirect utility of stopping at `t` with signal `Z_t = z`. -/
def X (t z : ℝ) : ℝ := max (p.gs 0 t z) (max (p.gs 1 t z) p.u₂)

/-- The normalized learning cost `ĉ = 2cσ²/(θ₁ − θ₀)²` (§4, p.19). -/
def chat : ℝ := 2 * p.c * p.σ ^ 2 / (p.θ₁ - p.θ₀) ^ 2

/-- `f̄(t, r) = (θ₁+θ₀)t/2 + σ²/(θ₁−θ₀) · log((1 − m̄₀)/m̄₀ · r/(1 − r))` (§4, p.21). It is the
signal level at which `m̄_t = r`. -/
def fUp (t r : ℝ) : ℝ :=
  (p.θ₁ + p.θ₀) / 2 * t + p.σ ^ 2 / (p.θ₁ - p.θ₀) * Real.log ((1 - p.mUp0) / p.mUp0 * (r / (1 - r)))

/-- `f̲(t, r) = (θ₁+θ₀)t/2 + σ²/(θ₁−θ₀) · log((1 − m̲₀)/m̲₀ · r/(1 − r))` (§4, p.21). It is the
signal level at which `m̲_t = r`. -/
def fLo (t r : ℝ) : ℝ :=
  (p.θ₁ + p.θ₀) / 2 * t + p.σ ^ 2 / (p.θ₁ - p.θ₀) * Real.log ((1 - p.mLo0) / p.mLo0 * (r / (1 - r)))

/-- The indifference point of §4, p.19: probabilities `π̲` (`πL`), `π̄` (`πU`) and a deterministic
signal trajectory `z̃` (`zt`) such that for every `t`, `π̲ = m̲_t(z̃_t)`, `π̄ = m̄_t(z̃_t)`, and
`π̲u₁₁ + (1 − π̲)u₁₀ = π̄u₀₁ + (1 − π̄)u₀₀`.

**Formalization Note.** The trajectory is a function of real `t`; the closed forms (12)–(13) make
sense for every real `t`, and the paper's trajectory on `t ≥ 0` is its restriction. Milestone
`indifference_exists_unique` shows that exactly one triple has this property. -/
def IsIndifference (πL πU : ℝ) (zt : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, πL = p.mLo t (zt t) ∧ πU = p.mUp t (zt t)) ∧
    πL * p.u 1 1 + (1 - πL) * p.u 1 0 = πU * p.u 0 1 + (1 - πU) * p.u 0 0

/-- The drift (46) of `Z` under the worst-case prior (arXiv:1708.01890v2, Lemma 5.1, p.26):
`θ̂` computed with the prior `m̄₀` when `z < z̃_t` and with `m̲₀` when `z ≥ z̃_t`. Named `drift` to
distinguish it from the boundary maps `f̄`, `f̲` of p.21 (the paper calls both `f`). -/
def drift (zt : ℝ → ℝ) (t z : ℝ) : ℝ :=
  if z < zt t then p.thetaHat p.mUp0 t z else p.thetaHat p.mLo0 t z

end Params

end EllsbergLearning


