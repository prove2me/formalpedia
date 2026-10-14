-- Prove2me | Definitions.Def_MLLangevin_ConvexA2_Setting
-- name    : MLLangevin_ConvexA2_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:53.31793+00:00
-- url     : https://prove2.me/theorems/0f4c64d4-3edd-4955-b97c-7b9d8a0ddf12
-- title:
--   (C_α), (2), (55), §2.4 and §5.1, pp. 1–2, 9, 30–32 — additive Euler scheme, pathwise diffusion, invariance of π and π^γ, [f]₁
-- statement:
--   This module fixes the additive Langevin-type setting of §2.4 and §5 of Egéa and Panloup.
--
--   Let $d\ge 0$, write $\mathbb R^d$ for the Euclidean space with norm $|\cdot|$ and inner product $\langle\cdot,\cdot\rangle$, let $b:\mathbb R^d\to\mathbb R^d$ be a drift, $\sigma$ a real number (the constant diffusion coefficient) and $W=(W_t)_{t\ge0}$ a $d$-dimensional process on a probability space $(\Omega,\mathcal F,\mathbb P)$. The module defines:
--
--   1. **Assumption $(\mathbf C_\alpha)$** (p. 9): for all $x,y\in\mathbb R^d$,
--   $$\langle b(y)-b(x),\,y-x\rangle\le-\alpha|x-y|^2 .$$
--   2. **The Euler scheme at its grid times** (2): for a step $\gamma>0$ and a start $x$, $\bar X^{\gamma,x}_0=x$ and
--   $$\bar X^{\gamma,x}_{(n+1)\gamma}=\bar X^{\gamma,x}_{n\gamma}+\gamma\,b(\bar X^{\gamma,x}_{n\gamma})+\sigma\big(W_{(n+1)\gamma}-W_{n\gamma}\big).$$
--   3. **The genuine continuous-time Euler scheme** (55): for $t\in[n\gamma,(n+1)\gamma)$, $\bar X^{\gamma,x}_t=\bar X^{\gamma,x}_{n\gamma}+(t-n\gamma)\,b(\bar X^{\gamma,x}_{n\gamma})+\sigma(W_t-W_{n\gamma})$.
--   4. **The diffusion** (pp. 30, 32): a process $X$ with continuous paths solves the additive SDE started at $x$ if, for every $\omega$ and $t\ge0$,
--   $$X_t=x+\int_0^t b(X_s)\,ds+\sigma W_t .$$
--   5. **Invariance of $\pi$ for the diffusion**: given a solution $X^x$ for each start $x$, a measure $\pi$ is invariant if $\int\mathbb P(X^x_t\in A)\,\pi(dx)=\pi(A)$ for every $t\ge0$ and Borel set $A$.
--   6. **Invariance of $\pi^\gamma$ for the Euler chain**: $\int\mathbb P\big(x+\gamma b(x)+\sigma\sqrt\gamma\,Z\in A\big)\,\pi^\gamma(dx)=\pi^\gamma(A)$ for every Borel set $A$, where $Z$ is a standard Gaussian vector of $\mathbb R^d$; this is the law of one step of the scheme driven by a Brownian motion.
--   7. **The Lipschitz constant** (p. 5): $[f]_1=\sup_{x\ne y}|f(x)-f(y)|/|x-y|$, written as the least $K\ge0$ with $|f(x)-f(y)|\le K|x-y|$ for all $x,y$.
--
--   These are the objects about which every statement of the mission is made: the diffusion whose invariant distribution $\pi$ is the target, and the Euler schemes that the multilevel estimator averages.
--
--   **Formalization Note** $\mathbb R^d$ is the published `EthierKurtz.SDEState d`. Times of $W$ are nonnegative reals; a real time $s$ is passed as `s.toNNReal`. The pathwise SDE is stated for every path, with continuous paths required so that the time integral is a genuine Lebesgue integral. The chain's invariance is stated through the standard Gaussian measure of Mathlib, which makes it independent of the particular Brownian motion. $[f]_1$ is an infimum of a nonempty set whenever $f$ is Lipschitz, which every statement using it assumes.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (2), p. 2; (C_α), §2.4, p. 9; (55) and the couple of §5.1.2, pp. 30, 32; [f]₁, §2.1, p. 5

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_MLLangevin_ConvexA1_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

open EthierKurtz

/-- The additive Euler scheme (2) with constant diffusion coefficient `σ` at its grid times:
`X̄_0 = x`, `X̄_{(n+1)γ} = X̄_{nγ} + γ b(X̄_{nγ}) + σ (W_{(n+1)γ} − W_{nγ})`.
The value at index `n` is the scheme at time `nγ`. -/
noncomputable def eulerChain {Ω : Type*} {d : ℕ} (b : SDEState d → SDEState d) (σ γ : ℝ)
    (x : SDEState d) (W : ℝ≥0 → Ω → SDEState d) : ℕ → Ω → SDEState d
  | 0 => fun _ => x
  | n + 1 => fun ω =>
      eulerChain b σ γ x W n ω + γ • b (eulerChain b σ γ x W n ω)
        + σ • (W (((n + 1 : ℕ) : ℝ) * γ).toNNReal ω - W (((n : ℕ) : ℝ) * γ).toNNReal ω)

/-- The genuine continuous-time Euler scheme (55), p. 32: for `t ∈ [nγ, (n+1)γ)`,
`X̄_t = X̄_{nγ} + (t − nγ) b(X̄_{nγ}) + σ (W_t − W_{nγ})`, where `n = ⌊t/γ⌋`. -/
noncomputable def eulerCont {Ω : Type*} {d : ℕ} (b : SDEState d → SDEState d) (σ γ : ℝ)
    (x : SDEState d) (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : SDEState d :=
  eulerChain b σ γ x W ⌊(t : ℝ) / γ⌋₊ ω
    + ((t : ℝ) - (⌊(t : ℝ) / γ⌋₊ : ℝ) * γ) • b (eulerChain b σ γ x W ⌊(t : ℝ) / γ⌋₊ ω)
    + σ • (W t ω - W (((⌊(t : ℝ) / γ⌋₊ : ℕ) : ℝ) * γ).toNNReal ω)

/-- `X` solves the additive SDE `X_t = x + ∫_0^t b(X_s) ds + σ W_t` pathwise
(pp. 30, 32), with continuous paths. -/
def IsAddSolution {Ω : Type*} {d : ℕ} (b : SDEState d → SDEState d) (σ : ℝ)
    (W : ℝ≥0 → Ω → SDEState d) (x : SDEState d) (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ ω, Continuous (fun t => X t ω)) ∧
  ∀ ω (t : ℝ≥0), X t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), b (X s.toNNReal ω)) + σ • W t ω

/-- `π` is invariant for the diffusion whose solution started at `x` is `Xsol x`:
`∫ P(X^x_t ∈ A) π(dx) = π(A)` for every time `t` and Borel set `A`. -/
def IsInvDiffusion {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d) (π : Measure (SDEState d)) : Prop :=
  ∀ (t : ℝ≥0) (A : Set (SDEState d)), MeasurableSet A →
    ∫⁻ x, P {ω | Xsol x t ω ∈ A} ∂π = π A

/-- `πγ` is invariant for the Euler chain with step `γ`: one step from `x` has the law of
`x + γ b(x) + σ √γ Z` with `Z` standard Gaussian on `ℝ^d`, and
`∫ ℙ(x + γ b(x) + σ√γ Z ∈ A) πγ(dx) = πγ(A)` for every Borel set `A`. -/
def IsInvChain {d : ℕ} (b : SDEState d → SDEState d) (σ γ : ℝ)
    (πγ : Measure (SDEState d)) : Prop :=
  ∀ A : Set (SDEState d), MeasurableSet A →
    ∫⁻ x, stdGaussian (SDEState d) {z | x + γ • b x + (σ * Real.sqrt γ) • z ∈ A} ∂πγ = πγ A

end MLLangevin.ConvexA2


