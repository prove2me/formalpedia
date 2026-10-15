-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Setting
-- name    : VolunteerEngage_Thresholds_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:53.173923+00:00
-- url     : https://prove2.me/theorems/1c68154e-fe13-4758-9fcc-699980849c5b
-- title:
--   §3–§4.1 — the engagement cost c (52), its conjugate ϕ (66), the Bellman equation (68)–(69), ĉ_l and the closed-form pieces u_l (p. 24)
-- statement:
--   This file fixes the objects of the drift-rate control problem of Ata, Tongarlak, Lee and Field on which the closed-form description of the Bellman solution is stated.
--
--   **Parameters.** There are $L$ engagement activities. The data are a lowest drift $\theta_0$, drift increments $\eta_1,\dots,\eta_L$, per-unit-drift costs $c_1,\dots,c_L$ (the $c_l=F_l/\eta_l$ of (50)), an idleness cost rate $p$, a mean-reversion rate $\kappa$ and a volatility $\sigma$ (the paper writes $\sigma^2$ in (59)–(69) for the workload variance $\sigma_w^2$). The **standing assumptions** are
--   $$L\ge1,\qquad \theta_0<0,\qquad \eta_l>0\ (l=1,\dots,L),\qquad 0<c_1<c_2<\dots<c_L<p,\qquad \kappa>0,\qquad \sigma>0$$
--   (so also $p>0$).
--
--   **Breakpoints and cost** ((51)–(52)). Let $\theta_l=\theta_0+\sum_{i=1}^{l}\eta_i$ and $A=[\theta_0,\theta_L]$. The engagement cost $c:A\to\mathbb R_+$ is the piecewise linear function with $c(\theta_0)=0$ and slope $c_l$ on $(\theta_{l-1},\theta_l]$:
--   $$c(x)=\sum_{i=1}^{l-1}c_i\eta_i+c_l(x-\theta_{l-1}),\qquad \theta_{l-1}<x\le\theta_l .$$
--
--   **Convex conjugate** (66): $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$, $y\in\mathbb R$.
--
--   **Bellman equation** (68)–(69). A constant $\beta>0$ and a continuously differentiable $v:[0,\infty)\to\mathbb R$ with derivative $v'$ solve the Bellman equation when
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0,$$
--   $v(0)=0$, $v$ is (strictly) increasing and $\lim_{x\to\infty}v(x)=p$.
--
--   **Shifted costs** (p. 22): $\hat c_l=c_l$ for $l=1,\dots,L$ and $\hat c_{L+1}=p$.
--
--   **Closed-form pieces** (p. 24). Given thresholds $\tau_1,\tau_2,\dots$ and a constant $\beta$, for $l=1,\dots,L+1$,
--   $$u_l(x)=p-\hat c_l\exp\Big\{\frac{-2\theta_{l-1}(x-\tau_l)+\kappa(x^2-\tau_l^2)}{\sigma^2}\Big\}+\frac{2(\beta-c(\theta_{l-1}))\sqrt\pi}{\sigma\sqrt\kappa}\exp\Big\{\frac{(\kappa x-\theta_{l-1})^2}{\kappa\sigma^2}\Big\}\Big[\Phi\Big(\frac{\kappa x-\theta_{l-1}}{\sigma\sqrt{\kappa/2}}\Big)-\Phi\Big(\frac{\kappa\tau_l-\theta_{l-1}}{\sigma\sqrt{\kappa/2}}\Big)\Big],$$
--   where $\Phi$ is the standard normal cumulative distribution function.
--
--   These are the objects of Proposition 3, which identifies the Bellman solution with $u_l$ on each threshold interval.
--
--   **Formalization Note** The parameters form a structure `Model`; $\eta$ and $c$ are sequences indexed by $\mathbb N$ of which only the indices $1,\dots,L$ are used. The standing assumptions are the predicate `Standing`; none is restated on p. 18 for the abstract problem, but all follow from the model's primitives ((24), (42), (43), (50), (15) and the ordering printed on p. 18). The cost (52) is written as one sum $\sum_{l=1}^L c_l\,(\min\{\theta_l,\max\{\theta_{l-1},x\}\}-\theta_{l-1})$, which equals (52) on $A$; values off $A$ are never used. $\phi$ is the supremum (66) over $A$ (a continuous function on a nonempty compact interval), not its closed form. A solution is a pair $(v,v')$ with $\beta>0$: $v'$ is continuous on $[0,\infty)$ and is the one-sided derivative of $v$ within $[0,\infty)$ at every $x\ge0$. "Increasing" is strict. $\Phi$ is the published `Cohen2019.Robust.Phi`, Mathlib's `cdf (gaussianReal 0 1)`. These definitions repeat the encodings of the companion mission on Theorem 1 (`VolunteerEngage.Bellman`), with $\hat c_l$ and $u_l$ added; the solution predicate here also includes the printed $\beta>0$ condition.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 18 (50)–(52), p. 21 (66), (68)–(69), p. 22 (71) ĉ_{L+1} = p, p. 24 definition of u_l

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace VolunteerEngage.Thresholds

open Filter Topology

/-! # The Bellman equation of the drift-rate control problem and its closed-form pieces

Ata, Tongarlak, Lee, Field, *A Dynamic Model for Managing Volunteer Engagement*,
arXiv:2312.02920v2: the parameters of the workload problem (§3–§4), the engagement cost `c(·)`
(52), its convex conjugate `ϕ` (66), the Bellman equation (68)–(69), the shifted costs `ĉ_l`
(p. 22, with `ĉ_{L+1} = p`) and the explicit functions `u_l` (p. 24). The standard normal
cumulative distribution function `Φ` is the published `Cohen2019.Robust.Phi`
(`cdf (gaussianReal 0 1)`). -/

/-- The parameters of the drift-rate control problem: `L` engagement activities, the lowest drift
`θ0`, the drift increments `η l` and per-unit-drift costs `c l` (used for `l = 1, …, L`; (43), (50)),
the idleness cost rate `p` (15), the mean-reversion rate `κ` (42) and the volatility `σ` of the
workload (`σ ^ 2` is the `σ²` of (59)–(69)). -/
structure Model where
  L : ℕ
  θ0 : ℝ
  η : ℕ → ℝ
  c : ℕ → ℝ
  p : ℝ
  κ : ℝ
  σ : ℝ

namespace Model

/-- The breakpoints `θ_l = θ0 + Σ_{i=1}^{l} η_i` of (51); `θ 0 = θ0`. -/
def θ (M : Model) (l : ℕ) : ℝ := M.θ0 + ∑ i ∈ Finset.Icc 1 l, M.η i

/-- Standing assumptions of the model: `L ≥ 1`; `θ0 < 0` ((24)); `η_l > 0` ((43));
`0 < c_1 < c_2 < ⋯ < c_L < p` ((50) and p. 18); `p > 0`, `κ > 0`, `σ > 0`. -/
def Standing (M : Model) : Prop :=
  1 ≤ M.L ∧ M.θ0 < 0 ∧ (∀ l ∈ Finset.Icc 1 M.L, 0 < M.η l) ∧
  0 < M.c 1 ∧ (∀ l ∈ Finset.Ico 1 M.L, M.c l < M.c (l + 1)) ∧ M.c M.L < M.p ∧
  0 < M.p ∧ 0 < M.κ ∧ 0 < M.σ

end Model

/-- The engagement cost `c(·)` of (52), written as one sum: the `l`-th summand is `c_l` times the
length of `[θ_{l-1}, θ_l] ∩ [θ_{l-1}, x]`. On `A = [θ0, θ_L]` this is (52): for
`θ_{m-1} < x ≤ θ_m` it equals `Σ_{i<m} c_i η_i + c_m (x - θ_{m-1})`, and `cost θ0 = 0`. Values off
`A` are never used. -/
def cost (M : Model) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 M.L, M.c l * (min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1))

/-- The convex conjugate (66): `ϕ(y) = sup_{x ∈ A} {y x - c(x)}` with `A = [θ0, θ_L]`. -/
noncomputable def phi (M : Model) (y : ℝ) : ℝ :=
  sSup ((fun x => y * x - cost M x) '' Set.Icc M.θ0 (M.θ M.L))

/-- `(β, v)` solves the Bellman equation (68)–(69), with `v'` the derivative of `v`:
`v` is continuously differentiable on `[0, ∞)` (one-sided derivative at `0`, `v'` continuous on
`[0, ∞)`), `β > 0`, `β = ½σ² v'(x) + xκ(p - v(x)) - ϕ(p - v(x))` for every `x ≥ 0` (68), `v(0) = 0`, `v` is
(strictly) increasing on `[0, ∞)` and `v(x) → p` as `x → ∞` (69). -/
def IsBellmanSol (M : Model) (β : ℝ) (v v' : ℝ → ℝ) : Prop :=
  0 < β ∧ ContinuousOn v' (Set.Ici 0) ∧
  (∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt v (v' x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → β = M.σ ^ 2 / 2 * v' x + x * M.κ * (M.p - v x) - phi M (M.p - v x)) ∧
  v 0 = 0 ∧ StrictMonoOn v (Set.Ici 0) ∧ Tendsto v atTop (𝓝 M.p)

/-- The costs `ĉ_l` of (71), p. 22: `ĉ_l = c_l` (the `c_l` of (50)) for `l = 1, …, L`, and
`ĉ_{L+1} = p`. -/
def chat (M : Model) (l : ℕ) : ℝ := if l = M.L + 1 then M.p else M.c l

/-- The function `u_l` of p. 24, for given thresholds `τ` (`τ l` is `τ_l`) and constant `β`:
`u_l(x) = p - ĉ_l exp{(-2θ_{l-1}(x - τ_l) + κ(x² - τ_l²))/σ²}
  + (2(β - c(θ_{l-1}))√π/(σ√κ)) exp{(κx - θ_{l-1})²/(κσ²)}
    [Φ((κx - θ_{l-1})/(σ√(κ/2))) - Φ((κτ_l - θ_{l-1})/(σ√(κ/2)))]`,
with `Φ` the standard normal cumulative distribution function. -/
noncomputable def u (M : Model) (β : ℝ) (τ : ℕ → ℝ) (l : ℕ) (x : ℝ) : ℝ :=
  M.p - chat M l * Real.exp ((-2 * M.θ (l - 1) * (x - τ l) + M.κ * (x ^ 2 - τ l ^ 2)) / M.σ ^ 2)
    + 2 * (β - cost M (M.θ (l - 1))) * Real.sqrt Real.pi / (M.σ * Real.sqrt M.κ)
      * Real.exp ((M.κ * x - M.θ (l - 1)) ^ 2 / (M.κ * M.σ ^ 2))
      * (Cohen2019.Robust.Phi ((M.κ * x - M.θ (l - 1)) / (M.σ * Real.sqrt (M.κ / 2)))
        - Cohen2019.Robust.Phi ((M.κ * τ l - M.θ (l - 1)) / (M.σ * Real.sqrt (M.κ / 2))))

end VolunteerEngage.Thresholds


