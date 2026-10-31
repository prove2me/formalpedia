-- Prove2me | Definitions.Def_ExitGamePrivate_Diffusion
-- name    : ExitGamePrivate_Diffusion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:48.350001+00:00
-- url     : https://prove2.me/theorems/acc17c49-f28b-4419-ba37-dfa453a3d5ea
-- title:
--   One-dimensional diffusion $dX_t=\mu(X_t)dt+b(X_t)dW_t$ on an open interval, Assumption 2.4, and the decreasing fundamental solution $\varphi$
-- statement:
--   This module fixes the stochastic setting of Kwon and Palczewski's exit game (§2, p.5).
--
--   A **diffusion on an interval** consists of a probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_t)$, a Brownian motion $W$, coefficients $\mu,b:\mathbb R\to\mathbb R$, the ends $x_L<x_U$ in $[-\infty,\infty]$ of the state interval $\mathcal I=(x_L,x_U)$, and a family $(X^x)_{x}$ of processes: $X^x_t(\omega)$ is the state at time $t$ of the solution of
--   $$dX_t=\mu(X_t)\,dt+b(X_t)\,dW_t,\qquad X_0=x. \tag{2.1}$$
--
--   The diffusion is **regular** when:
--   1. $\mathcal I$ is nonempty;
--   2. on every horizon $[0,T]$, $(\Omega,\mathcal F,P,(\mathcal F_t),W)$ is a Brownian probability space satisfying the usual conditions (completeness and right-continuity);
--   3. (Assumption 2.4) $\mu$ and $b$ are Lipschitz continuous on $\mathcal I$ and $b>0$ on $\mathcal I$;
--   4. for every $x\in\mathcal I$, $X^x$ is a strong solution of (2.1) from $x$ on every horizon;
--   5. the boundaries of $\mathcal I$ are not attainable: almost surely $X^x_t\in\mathcal I$ for all $t\ge0$.
--
--   The module also defines the discount $e^{-r\tau}$ of a random time $\tau\in[0,\infty]$ with $e^{-r\cdot\infty}=0$, the window $[0,\tau)$, the hitting time $H_y=\inf\{t\ge0:X^x_t=y\}$, and the **decreasing fundamental solution** $\varphi$ of $(\mathcal L_X-r)\varphi=0$, $\mathcal L_X=\tfrac12 b^2\partial_x^2+\mu\partial_x$, normalised at a reference point $c\in\mathcal I$:
--   $$\varphi_c(x)=\begin{cases}E_x\big[e^{-rH_c}\big], & x\ge c,\\[2pt] 1\big/E_c\big[e^{-rH_x}\big], & x<c.\end{cases}$$
--
--   These objects underlie every statement of the mission: the payoffs, the single-player threshold $\alpha$ and the belief process are all built on them.
--
--   **Formalization Note** Time and the filtration are indexed by $\mathbb R$ so that the platform's `EntropyMFG.Enhanced.BrownianOn` and `StrongSolution` apply directly; stopping times use the restriction of the filtration to $\mathbb R_{\ge0}$ and take values in $[0,\infty]$. The paper's $\varphi$ is defined only up to a positive factor; the hitting-time formula (Borodin–Salminen, II.10) fixes the factor by $\varphi_c(c)=1$. Formula (3.3) writes $\sigma^2(x)$ for $b^2(x)$.
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, §2 p.5 ((2.1), model and boundary conditions), Assumption 2.4 p.6, §3 p.8 (decreasing fundamental solution, (3.3))

import Mathlib
import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ExitGamePrivate

/-- The discount factor `e^{-r τ}` of a random time `τ ∈ [0, ∞]`, with the convention
`e^{-r·∞} = 0`.

Kwon & Palczewski, *Exit Game with Private Information*, arXiv:2210.01610v2, used in the payoffs
`J₁, J₂` (p.6), (2.3) (p.7), (3.1) (p.8), (4.15) and (4.17) (p.17).

**Formalization Note** Stopping times take values in `WithTop ℝ≥0`, with `⊤` the time `+∞`.
`disc r ⊤ = 0`, so every term `e^{-rτ}·(…)` vanishes on `{τ = ∞}`, as in the paper; the cast
`⊤ ↦ 0` of `WithTop.untopD 0` (which would give `e^{0} = 1`) is never used for a discount. -/
def disc (r : ℝ) : WithTop ℝ≥0 → ℝ
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-(r * t))

/-- The time window `[0, τ)` of a random time `τ ∈ [0, ∞]`, as a set of real times
(`[0, ∞)` when `τ = ⊤`). The integrals `∫_0^τ … dt` of the paper are set integrals over it. -/
def window (τ : WithTop ℝ≥0) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) < τ}

/-- A one-dimensional diffusion `dXₜ = μ(Xₜ)dt + b(Xₜ)dWₜ` on an open interval
`𝓘 = (x_L, x_U)` with possibly infinite ends, together with the probability space carrying it.

Kwon & Palczewski, arXiv:2210.01610v2, §2, (2.1), p.5: "Consider a complete probability space
(Ω, F, P) with filtration (Fₜ)ₜ≥₀ satisfying the usual conditions. The underlying state of the
system is described by a one-dimensional diffusion (2.1) dXₜ = µ(Xₜ)dt + b(Xₜ)dWₜ, … We denote by
I = (x_L, x_U) the (potentially infinite) interval in which Xₜ takes values".

Fields: the probability measure `P`, the filtration `𝔽` (indexed by `ℝ`; only `t ≥ 0` is used),
the Brownian motion `W`, the ends `xL, xU ∈ [-∞, ∞]` of `𝓘`, the coefficients `μ, b`, and the
family of solutions: `X x t ω` is the state at time `t` of the solution started at `X₀ = x`
(the paper's `Xˣₜ`, p.16).

**Formalization Note** Time is real; the filtration and the processes are indexed by `ℝ` so that
the reused platform definitions `EntropyMFG.Enhanced.BrownianOn` and `StrongSolution` (which index
time by `ℝ` on a horizon `[0, T]`) apply verbatim; `filt` restricts the filtration to `ℝ≥0` for
stopping times. The family `X` is data; `IsRegular` asserts that each `X x` is a strong solution
from `x`. -/
structure Diffusion (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  𝔽 : Filtration ℝ ‹MeasurableSpace Ω›
  W : ℝ → Ω → ℝ
  xL : EReal
  xU : EReal
  μ : ℝ → ℝ
  b : ℝ → ℝ
  X : ℝ → ℝ → Ω → ℝ

namespace Diffusion

variable {Ω : Type*} [MeasurableSpace Ω] (Dif : Diffusion Ω)

/-- The state interval `𝓘 = (x_L, x_U)` (p.5), with `x_L, x_U ∈ [-∞, ∞]`. -/
def I : Set ℝ := {x : ℝ | Dif.xL < (x : EReal) ∧ (x : EReal) < Dif.xU}

/-- The filtration `(Fₜ)_{t ≥ 0}` indexed by `ℝ≥0`, so that `(Fₜ)`-stopping times are
`WithTop ℝ≥0`-valued (Mathlib's `IsStoppingTime`). -/
def filt : Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := Dif.𝔽 (t : ℝ)
  mono' _ _ h := Dif.𝔽.mono (by exact_mod_cast h)
  le' t := Dif.𝔽.le (t : ℝ)

/-- The setting of §2 together with Assumption 2.4, p.5–6.

1. `𝓘` is a nonempty interval;
2. on every horizon `[0, T]`, `(Ω, F, P, (Fₜ), W)` is a Brownian probability space with the usual
   conditions (`P` a probability measure, `F₀` contains the `P`-null sets, `(Fₜ)` right-continuous,
   `W` an `(Fₜ)`-Brownian motion);
3. Assumption 2.4: `μ` and `b` are Lipschitz continuous on `𝓘` and `b > 0` on `𝓘`;
4. for every `x ∈ 𝓘` and every horizon `T`, `X x` is a strong solution of (2.1) with `X₀ = x`;
5. the boundaries of `𝓘` are not attainable: for every `x ∈ 𝓘`, almost surely `Xˣₜ ∈ 𝓘` for
   every `t ≥ 0`.

**Formalization Note** "Complete probability space with the usual conditions" is the completeness
and right-continuity built into `EntropyMFG.Enhanced.BrownianOn` (null sets in `F₀`), required on
every horizon. Strong uniqueness of `X` follows from 3 and is not assumed. Nonemptiness of `𝓘`
only excludes the degenerate case in which the state space is empty. -/
structure IsRegular : Prop where
  nonempty : Dif.I.Nonempty
  brownian : ∀ T : ℝ, 0 < T → EntropyMFG.Enhanced.BrownianOn Dif.P Dif.𝔽 Dif.W T
  lipschitz_μ : ∃ K : ℝ≥0, LipschitzOnWith K Dif.μ Dif.I
  lipschitz_b : ∃ K : ℝ≥0, LipschitzOnWith K Dif.b Dif.I
  b_pos : ∀ x ∈ Dif.I, 0 < Dif.b x
  strong : ∀ x ∈ Dif.I, ∀ T : ℝ, 0 < T →
    EntropyMFG.Enhanced.StrongSolution Dif.P Dif.𝔽 Dif.W 0 T (fun _ => x)
      (fun _ _ y => Dif.μ y) (fun _ _ y => Dif.b y) (Dif.X x)
  stays : ∀ x ∈ Dif.I, ∀ᵐ ω ∂Dif.P, ∀ t : ℝ, 0 ≤ t → Dif.X x t ω ∈ Dif.I

/-- The first hitting time `H_y = inf{t ≥ 0 : Xˣₜ = y}` of the level `y` by the diffusion
started at `x` (`⊤` if the level is never hit). -/
def hitTime (x y : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (fun (t : ℝ≥0) ω => Dif.X x (t : ℝ) ω) {y} 0

/-- The decreasing fundamental solution `φ` of `(𝓛_X − r)φ = 0` (p.8, before (3.3)), normalised
by `φ(c) = 1` at a reference point `c ∈ 𝓘`:
`φ(x) = Eₓ[e^{-r H_c}]` for `x ≥ c` and `φ(x) = 1 / E_c[e^{-r H_x}]` for `x < c`.

Kwon & Palczewski, arXiv:2210.01610v2, p.8: "Let φ(·) denote the decreasing fundamental solution
to the ordinary differential equation (𝓛_X − r)φ(x) = 0, where 𝓛_X is the generator of (Xₜ)".

**Formalization Note** The decreasing fundamental solution is determined only up to a positive
factor, and at an entrance boundary the ODE alone does not single it out. This is the
probabilistic characterisation (Borodin–Salminen, *Handbook of Brownian Motion*, II.10): for
`x ≥ y`, `Eₓ[e^{-r H_y}] = φ(x)/φ(y)`. Changing `c` multiplies `φ` by a positive constant. The
generator is `𝓛_X = ½ b(x)² ∂² + µ(x) ∂` ((3.3) prints `σ²(x)` for the diffusion coefficient,
which is `b(x)²`). -/
def phi (r c x : ℝ) : ℝ :=
  if c ≤ x then ∫ ω, disc r (Dif.hitTime x c ω) ∂Dif.P
  else 1 / ∫ ω, disc r (Dif.hitTime c x ω) ∂Dif.P

end Diffusion

end ExitGamePrivate


