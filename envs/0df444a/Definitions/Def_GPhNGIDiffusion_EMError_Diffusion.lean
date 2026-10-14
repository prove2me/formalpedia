-- Prove2me | Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
-- name    : GPhNGIDiffusion_EMError_Diffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:24.931491+00:00
-- url     : https://prove2.me/theorems/9ccb6584-c0a3-43b3-8ac1-8c2b61bfa630
-- title:
--   Additive-noise SDE $dX_t=b(X_t)dt+\sigma dB_t$: solutions, transition function $P_t$, invariant measures, generator $\mathcal A$, Stein solution
-- statement:
--   Let $b:\mathbb R^d\to\mathbb R^d$ and $\sigma\in\mathbb R^{d\times d}$. On a probability space carrying a standard $d$-dimensional Brownian motion $(B_t)_{t\ge0}$, a process $(X_t)_{t\ge 0}$ is a **solution started at $x$** of
--   $$
--   dX_t=b(X_t)\,dt+\sigma\,dB_t
--   $$
--   if its paths are continuous and, for every outcome and every $t\ge0$,
--   $$
--   X_t=x+\int_0^t b(X_s)\,ds+\sigma B_t .
--   $$
--   A family $P_t(x,\cdot)$ of probability measures is the **transition function** of the equation if, on every such probability space, every solution started at $x$ has law $P_t(x,\cdot)$ at time $t$. The dual action on measures is $(P_t^*\nu)(A)=\int P_t(x,A)\,\nu(dx)$, and $\mu$ is an **invariant probability measure** if $P_t^*\mu=\mu$ for all $t\ge0$.
--
--   The **generator** acts on $f\in C^2(\mathbb R^d,\mathbb R)$ by
--   $$
--   \mathcal Af(y)=\langle\nabla f(y),b(y)\rangle+\tfrac12\langle\sigma\sigma',\nabla^2 f(y)\rangle_{\mathrm{HS}},
--   $$
--   with $\partial_i f$ and $\partial_{ij}f$ the first and second partial derivatives. For a test function $h$, the **Stein solution** is
--   $$
--   f(x)=-\int_0^\infty\big(P_th(x)-\mu(h)\big)\,dt,\qquad P_th(x)=\int h(y)\,P_t(x,dy).
--   $$
--
--   For the model's drift $g$ these are the transition function, invariant measure, generator (1.4) and Stein equation solution of the limiting diffusion (1.1).
--
--   **Formalization Note** The noise is additive, so the equation is a pathwise integral equation and needs no Itô integral. For globally Lipschitz $b$ the solution exists and is pathwise unique, so the transition function is determined by this property and does not depend on the probability space. Time is `ℝ≥0`. The Brownian motion is the published `EthierKurtz.IsStandardBrownian`. The Stein solution is the representation (3.2) of the paper; for Lipschitz $h$ it is well defined by the exponential ergodicity of Lemma A.1.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 2, (1.1); p. 7, P_t and generator (1.4); p. 8, P*_t; p. 9, (2.1); p. 12, (3.2)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model

open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace GPhNGIDiffusion.EMError

variable {d : ℕ}

/-- `X` is a solution of the additive-noise SDE `dX_t = b(X_t) dt + σ dB_t` started at `x`, driven by
`B`: its paths are continuous and, for every `ω` and every `t ≥ 0`,
`X_t = x + ∫₀ᵗ b(X_s) ds + σ B_t` (the integral form of (1.1); the noise is additive, so no stochastic
integral is needed). -/
def SolvesAdditiveSDE {Ω : Type*} (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (B X : ℝ≥0 → Ω → EthierKurtz.SDEState d)
    (x : EthierKurtz.SDEState d) : Prop :=
  (∀ ω, Continuous fun t => X t ω) ∧
    ∀ ω (t : ℝ≥0), X t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), b (X (Real.toNNReal s) ω)) + mv σ (B t ω)

/-- `P` is the transition function `P_t(x, ·)` of `dX_t = b(X_t) dt + σ dB_t` (§1.4, p. 7): on every
probability space carrying a standard `d`-dimensional Brownian motion `B`, every solution started at
`x` has law `P t x` at time `t`. For globally Lipschitz `b` the solution exists and is pathwise
unique, so this determines `P`. -/
def IsTransitionFunction (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d)) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState d) (x : EthierKurtz.SDEState d),
    EthierKurtz.IsStandardBrownian Pr B → SolvesAdditiveSDE b σ B X x →
    ∀ t, Pr.map (X t) = P t x

/-- The dual action `P*_t ν = ∫ P_t(x, ·) ν(dx)` (p. 8). -/
noncomputable def dualAction (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (t : ℝ≥0) (ν : Measure (EthierKurtz.SDEState d)) : Measure (EthierKurtz.SDEState d) :=
  ν.bind (P t)

/-- `µ` is an invariant probability measure of the transition function `P`:
`P*_t µ = µ` for every `t ≥ 0`. -/
def IsInvariantMeasure (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (μ : Measure (EthierKurtz.SDEState d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t, dualAction P t μ = μ

/-- The second partial derivative `∂_{ij} f(y)` (the `(i, j)` entry of the Hessian `∇²f(y)`). -/
noncomputable def partial2 (f : EthierKurtz.SDEState d → ℝ) (i j : Fin d)
    (y : EthierKurtz.SDEState d) : ℝ :=
  iteratedFDeriv ℝ 2 f y ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

/-- The first partial derivative `∂_i f(y)`. -/
noncomputable def partial1 (f : EthierKurtz.SDEState d → ℝ) (i : Fin d)
    (y : EthierKurtz.SDEState d) : ℝ :=
  fderiv ℝ f y (EuclideanSpace.single i 1)

/-- The generator (1.4), p. 7, of `dX_t = b(X_t) dt + σ dB_t`:
`Af(y) = ⟨∇f(y), b(y)⟩ + ½ ⟨σσ′, ∇²f(y)⟩_HS`. It is only meaningful for `f ∈ C²`; every statement
using it on a function assumes or concludes that regularity. -/
noncomputable def generator (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (f : EthierKurtz.SDEState d → ℝ)
    (y : EthierKurtz.SDEState d) : ℝ :=
  ⟪gradient f y, b y⟫ + (1 / 2) * ∑ i, ∑ j, (σ * σᵀ) i j * partial2 f i j y

/-- The solution of the Stein equation `Af = h − µ(h)` given by the semigroup representation
`f(x) = −∫₀^∞ (P_t h(x) − µ(h)) dt`, where `P_t h(x) = ∫ h(y) P_t(x, dy)` ((3.2), p. 12). -/
noncomputable def steinSolution
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (μ : Measure (EthierKurtz.SDEState d)) (h : EthierKurtz.SDEState d → ℝ)
    (x : EthierKurtz.SDEState d) : ℝ :=
  -∫ t in Set.Ioi (0 : ℝ), ((∫ y, h y ∂(P (Real.toNNReal t) x)) - ∫ y, h y ∂μ)

end GPhNGIDiffusion.EMError


