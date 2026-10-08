-- Prove2me | Definitions.Def_GJNSteadyState_Interchange_Lyapunov
-- name    : GJNSteadyState_Interchange_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:10.815983+00:00
-- url     : https://prove2.me/theorems/9119595b-b274-4094-b179-60a959b76c94
-- title:
--   Definition 2 and (24)–(26), p. 15 — Lyapunov and geometric Lyapunov functions, φ(t), L₁(θ, t), L₂(θ, t)
-- statement:
--   Let $(\Xi(t):t\ge0)$ be a Markov process on a state space $\mathcal X$, write $\mathbb E_x$ for the expectation when $\Xi(0)=x$, and fix a drift time $t_0>0$. For $\Phi:\mathcal X\to\mathbb R_+$:
--
--   1. $\Phi$ is a **Lyapunov function** with drift size parameter $-\gamma<0$, drift time $t_0$ and exception parameter $K$ if
--   $$\sup_{x:\,\Phi(x)>K}\big\{\mathbb E_x\Phi(\Xi(t_0))-\Phi(x)\big\}\le-\gamma. \tag{22}$$
--   2. $\Phi$ is a **geometric Lyapunov function** with geometric drift size $0<\gamma<1$, drift time $t_0$ and exception parameter $K$ if
--   $$\sup_{x:\,\Phi(x)>K}\big\{\Phi(x)^{-1}\mathbb E_x\Phi(\Xi(t_0))\big\}\le\gamma. \tag{23}$$
--   3. For $\theta>0$,
--   $$\phi(t_0)=\sup_x\Phi(x)^{-1}\mathbb E_x\Phi(\Xi(t_0)),\quad L_1(\theta,t_0)=\sup_x\mathbb E_x\big[e^{\theta(\Phi(\Xi(t_0))-\Phi(x))}\big],$$
--   $$L_2(\theta,t_0)=\sup_x\mathbb E_x\big[(\Phi(\Xi(t_0))-\Phi(x))^2e^{\theta(\Phi(\Xi(t_0))-\Phi(x))^+}\big]. \tag{24–26}$$
--   These may be $+\infty$.
--
--   These notions drive the paper's bounds on stationary distributions (Theorems 5 and 6), which are then applied to the generalized Jackson network with $\Phi(z,a,v)=w'z$.
--
--   **Formalization Note** The drift time $t_0$ is encoded in an expectation operator $E(x,f) = \mathbb E_x f(\Xi(t_0))$ on nonnegative functions with values in $[0,\infty]$: for a general Markov process it is the time-$t_0$ transition kernel (`kernelExp`), for the network it is `expectAt` at time $nt_0$. Condition (22) is written $\mathbb E_x\Phi(\Xi(t_0))+\gamma\le\Phi(x)$ for $\Phi(x)>K$ (false when the expectation is infinite, as on the page). $\phi$, $L_1$, $L_2$ are extended nonnegative reals, with $\Phi(x)^{-1}=\infty$ when $\Phi(x)=0$, matching "it is not excluded that $\phi(t)=\infty$".
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 15, Definition 2, (22)–(26); p. 14, Section 3.1 (E_x)

import Mathlib

open MeasureTheory

namespace GJNSteadyState.Interchange

/-!
Gamarnik–Zeevi (2006), Definition 2 and (24)–(26), p. 15: Lyapunov functions for a Markov
process `Ξ` on a state space `𝒳`. The objects are stated for a fixed drift time `t₀` through an
expectation operator `E x f = E_x f(Ξ(t₀))` (an `ℝ≥0∞`-valued expectation of a nonnegative
function, started from `Ξ(0) = x`). For a general Markov process `E` comes from the time-`t₀`
transition kernel (`kernelExp`); for the GJN it is `expectAt`.
-/

/-- The expectation operator `x, f ↦ ∫ f dκ(x)` of a transition kernel `κ`. -/
noncomputable def kernelExp {X : Type*} [MeasurableSpace X] (κ : ProbabilityTheory.Kernel X X)
    (x : X) (f : X → ENNReal) : ENNReal :=
  ∫⁻ y, f y ∂(κ x)

/-- (22): `Φ : 𝒳 → ℝ₊` is a Lyapunov function with drift size parameter `−γ < 0` and exception
parameter `K` (at the drift time encoded in `E`): `E_x Φ(Ξ(t₀)) − Φ(x) ≤ −γ` for every `x` with
`Φ(x) > K`. -/
def IsLyapunov {X : Type*} (E : X → (X → ENNReal) → ENNReal) (Φ : X → NNReal) (γ K : ℝ) :
    Prop :=
  0 < γ ∧ ∀ x, K < (Φ x : ℝ) → E x (fun y => (Φ y : ENNReal)) + ENNReal.ofReal γ ≤ Φ x

/-- (23): `Φ` is a geometric Lyapunov function with geometric drift size `0 < γ < 1` and
exception parameter `K`: `Φ(x)⁻¹ E_x Φ(Ξ(t₀)) ≤ γ` for every `x` with `Φ(x) > K`. -/
def IsGeomLyapunov {X : Type*} (E : X → (X → ENNReal) → ENNReal) (Φ : X → NNReal) (γ K : ℝ) :
    Prop :=
  0 < γ ∧ γ < 1 ∧
    ∀ x, K < (Φ x : ℝ) → E x (fun y => (Φ y : ENNReal)) ≤ ENNReal.ofReal γ * Φ x

/-- (24): `φ = sup_x Φ(x)⁻¹ E_x Φ(Ξ(t))`, possibly `∞` (with `0⁻¹ = ∞`). -/
noncomputable def phiSup {X : Type*} (E : X → (X → ENNReal) → ENNReal) (Φ : X → NNReal) :
    ENNReal :=
  ⨆ x, ((Φ x : ENNReal))⁻¹ * E x (fun y => (Φ y : ENNReal))

/-- (25): `L₁(θ) = sup_x E_x[exp(θ(Φ(Ξ(t)) − Φ(x)))]`. -/
noncomputable def L1 {X : Type*} (E : X → (X → ENNReal) → ENNReal) (Φ : X → NNReal) (θ : ℝ) :
    ENNReal :=
  ⨆ x, E x (fun y => ENNReal.ofReal (Real.exp (θ * ((Φ y : ℝ) - Φ x))))

/-- (26): `L₂(θ) = sup_x E_x[(Φ(Ξ(t)) − Φ(x))² exp(θ(Φ(Ξ(t)) − Φ(x))⁺)]`. -/
noncomputable def L2 {X : Type*} (E : X → (X → ENNReal) → ENNReal) (Φ : X → NNReal) (θ : ℝ) :
    ENNReal :=
  ⨆ x, E x (fun y => ENNReal.ofReal
    (((Φ y : ℝ) - Φ x) ^ 2 * Real.exp (θ * max ((Φ y : ℝ) - Φ x) 0)))

end GJNSteadyState.Interchange


