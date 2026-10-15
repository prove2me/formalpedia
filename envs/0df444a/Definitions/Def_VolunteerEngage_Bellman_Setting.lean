-- Prove2me | Definitions.Def_VolunteerEngage_Bellman_Setting
-- name    : VolunteerEngage_Bellman_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:46.127779+00:00
-- url     : https://prove2.me/theorems/c85b8a4c-52f0-4130-8d24-e70ca8f0037c
-- title:
--   §3–§4 and Online Supplement §F — the engagement cost c (52), its conjugate ϕ (66), the Bellman equation (68)–(69), IVP(β), β̲, I, D, β∗
-- statement:
--   This file sets up the drift-rate control problem's Bellman equation from Ata, Tongarlak, Lee and Field, and the objects of the shooting argument used to solve it.
--
--   **Parameters.** There are $L$ engagement activities. The data are a lowest drift $\theta_0$, drift increments $\eta_1,\dots,\eta_L$, per-unit-drift costs $c_1,\dots,c_L$, an idleness cost rate $p$, a mean-reversion rate $\kappa$ and a volatility $\sigma$. The **standing assumptions** are
--
--   1. $L\ge1$ and $\theta_0<0$;
--   2. $\eta_l>0$ for $l=1,\dots,L$;
--   3. $0<c_1<c_2<\dots<c_L<p$;
--   4. $p>0$, $\kappa>0$, $\sigma>0$.
--
--   **Cost and conjugate.** The breakpoints are $\theta_l=\theta_0+\sum_{i=1}^{l}\eta_i$ $(l=0,\dots,L)$, and $A=[\theta_0,\theta_L]$. The engagement cost $c:A\to\mathbb R_+$ is the piecewise linear function with $c(\theta_0)=0$ and slope $c_l$ on $(\theta_{l-1},\theta_l]$:
--
--   $$c(x)=\sum_{i=1}^{l-1}c_i\eta_i+c_l(x-\theta_{l-1}),\qquad \theta_{l-1}< x\le\theta_l .$$
--
--   Its convex conjugate is
--
--   $$\phi(y)=\sup_{x\in A}\{yx-c(x)\},\qquad y\in\mathbb R .$$
--
--   **Bellman equation.** A pair $(\beta,v)$ solves the Bellman equation (68)–(69) if $v$ is continuously differentiable on $[0,\infty)$, $v(0)=0$, $v$ is strictly increasing on $[0,\infty)$, $v(x)\to p$ as $x\to\infty$, and
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0 .$$
--
--   **Shooting objects.** For $\beta\in\mathbb R$, IVP($\beta$) is the same equation with only the initial condition $v(0)=0$ (no monotonicity, no limit). Further,
--
--   $$\underline\beta=-\inf\{\phi(y):y\le p\},$$
--
--   $\mathcal I=\{\beta>\underline\beta:$ IVP($\beta$) has a strictly increasing solution$\}$, $\mathcal D=\{\beta>\underline\beta:$ IVP($\beta$) has a solution $v$ and there is $x_\beta$ with $v$ nondecreasing on $(0,x_\beta)$ and nonincreasing on $(x_\beta,\infty)\}$, and $\beta^*=\inf\mathcal I$.
--
--   These are the objects of Theorem 1 and of the lemmas of Online Supplement §F.
--
--   **Formalization Note.**
--   1. $\eta$ and $c$ are sequences indexed by $\mathbb N$, used only at $1,\dots,L$.
--   2. The cost is written as one sum $\sum_{l=1}^{L}c_l\,(\min(\theta_l,\max(\theta_{l-1},x))-\theta_{l-1})$. It equals (52) on $A$, and its values off $A$ are never used.
--   3. $\phi$ is the real supremum over the compact interval $A$ (nonempty under the standing assumptions), so it is attained. It is not defined by its closed form.
--   4. The paper writes $\underline\beta=-\inf_y\phi(y)$. Over all $y\in\mathbb R$ this infimum is $-\infty$ when $\theta_L<0$, but the paper's proofs treat that case using $\inf_{y\le p}\phi(y)$. The Setting takes the infimum over $y\le p$, where it is finite and attained. This equals the printed value whenever $\theta_L\ge0$.
--   5. "Continuously differentiable on $[0,\infty)$" is a pair $(v,v')$ with $v'$ continuous on $[0,\infty)$ and $v'(x)$ the derivative of $v$ within $[0,\infty)$ at every $x\ge0$. "Increasing" is strict.
--   6. $\beta^*$ is a real `sInf`; the milestones (Lemmas 13, 17, 18) are what make it meaningful.
--   7. The standing assumptions are implicit in the paper: they follow from the queueing model's primitives ((24), (43), (50), p. 18) and are stated as an explicit predicate here.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 14 (24), p. 18 (50)–(52), p. 21 (66), (68)–(69); Online Supplement p. 13 (β̲, before (F10)), p. 14 (F10)–(F11) and the definitions of I and D, p. 17 β∗ = inf I

import Mathlib

namespace VolunteerEngage.Bellman

open Filter Topology

/-! # The drift-rate control problem's Bellman equation (Ata, Tongarlak, Lee, Field)

Parameters of the workload problem (§3–§4 of arXiv:2312.02920v2), the engagement cost `c(·)` (52),
its convex conjugate `ϕ` (66), the Bellman equation (68)–(69), and the shooting objects of Online
Supplement §F: the lower bound `β̲`, the initial value problem IVP(β) (F10)–(F11), the sets `I`
and `D`, and `β* = inf I`. -/

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
`[0, ∞)`), `β = ½σ² v'(x) + xκ(p - v(x)) - ϕ(p - v(x))` for every `x ≥ 0` (68), `v(0) = 0`, `v` is
(strictly) increasing on `[0, ∞)` and `v(x) → p` as `x → ∞` (69). -/
def IsBellmanSol (M : Model) (β : ℝ) (v v' : ℝ → ℝ) : Prop :=
  ContinuousOn v' (Set.Ici 0) ∧
  (∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt v (v' x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → β = M.σ ^ 2 / 2 * v' x + x * M.κ * (M.p - v x) - phi M (M.p - v x)) ∧
  v 0 = 0 ∧ StrictMonoOn v (Set.Ici 0) ∧ Tendsto v atTop (𝓝 M.p)

/-- The lower bound `β̲ = -inf {ϕ(y) : y ≤ p}` (Online Supplement p. 13, before (F10)), in the
corrected reading: the infimum is taken over `y ≤ p`, where it is finite and attained. It equals
the printed `-inf_{y ∈ ℝ} ϕ(y)` whenever `θ_L ≥ 0`. -/
noncomputable def betaLow (M : Model) : ℝ :=
  -sInf (phi M '' Set.Iic M.p)

/-- `(v, v')` solves the initial value problem IVP(β) (F10)–(F11): `v` is continuously
differentiable on `[0, ∞)` with derivative `v'`, `β = ½σ² v'(x) + xκ(p - v(x)) - ϕ(p - v(x))` for
every `x ≥ 0` (F10), and `v(0) = 0` (F11). -/
def IsIVPSol (M : Model) (β : ℝ) (v v' : ℝ → ℝ) : Prop :=
  ContinuousOn v' (Set.Ici 0) ∧
  (∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt v (v' x) (Set.Ici 0) x) ∧
  (∀ x : ℝ, 0 ≤ x → β = M.σ ^ 2 / 2 * v' x + x * M.κ * (M.p - v x) - phi M (M.p - v x)) ∧
  v 0 = 0

/-- The set `I = {β > β̲ : v_β is increasing}` (Online Supplement p. 14). -/
def Iset (M : Model) : Set ℝ :=
  {β | betaLow M < β ∧ ∃ v v' : ℝ → ℝ, IsIVPSol M β v v' ∧ StrictMonoOn v (Set.Ici 0)}

/-- The set `D = {β > β̲ : ∃ x_β, v_β is nondecreasing on (0, x_β) and nonincreasing on
(x_β, ∞)}` (Online Supplement p. 14). -/
def Dset (M : Model) : Set ℝ :=
  {β | betaLow M < β ∧ ∃ v v' : ℝ → ℝ, IsIVPSol M β v v' ∧
    ∃ xβ : ℝ, MonotoneOn v (Set.Ioo 0 xβ) ∧ AntitoneOn v (Set.Ioi xβ)}

/-- `β* = inf I` (Online Supplement p. 17). -/
noncomputable def betaStar (M : Model) : ℝ := sInf (Iset M)

end VolunteerEngage.Bellman


