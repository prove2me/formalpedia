-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
-- name    : GPhNGIDiffusion_OccupationCLT_Diffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:36.578317+00:00
-- url     : https://prove2.me/theorems/de7b5ac7-9146-4bc1-a0da-e92e8f0be7cc
-- title:
--   (1.1) and §1.4 — the limiting diffusion as a pathwise solution, its semigroup P_t and invariant measures
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space carrying a standard $d$-dimensional Brownian motion $(B_t)_{t\ge0}$ with continuous paths. For a drift $b:\mathbb R^d\to\mathbb R^d$ and a matrix $\sigma$, a **solution flow** of $dX_t=b(X_t)\,dt+\sigma\,dB_t$ is a family $(X^x_t)_{x\in\mathbb R^d,t\ge0}$ such that for every $x$ and every $\omega$ the path $t\mapsto X^x_t(\omega)$ is continuous and
--   $$
--   X^x_t=x+\int_0^t b(X^x_s)\,ds+\sigma B_t,\qquad t\ge0 .
--   $$
--   Because the noise is additive this is a pathwise integral equation. The triple $(\mathbb P,B,X)$ **realizes the limiting diffusion** (1.1) of a model if $\mathbb P$ is a probability measure, $B$ is a standard Brownian motion under $\mathbb P$, and $X$ is a solution flow with $b=g$.
--
--   The **Markov semigroup** is $P_tf(x)=\mathbb E f(X^x_t)$, and a measure $\mu$ on $\mathbb R^d$ is **invariant** if
--   $$
--   \int_{\mathbb R^d}\mathbb P(X^x_t\in A)\,\mu(dx)=\mu(A)\qquad\text{for all }t\ge0\text{ and Borel }A .
--   $$
--
--   Since $g$ is globally Lipschitz, the solution flow exists and is unique for every continuous path, so the law $P_t(x,\cdot)$ of $X^x_t$ does not depend on the chosen probability space; by Dieker and Gao [19, Theorem 3] the diffusion has a unique invariant probability measure.
--
--   **Formalization Note** Brownian motion is the published predicate `EthierKurtz.IsStandardBrownian` (time $\mathbb R_{\ge0}$, continuous paths for every $\omega$, independent real Brownian coordinates). Every theorem of the mission takes $(\Omega,\mathbb P,B,X)$ and an invariant probability measure $\mu$ as hypotheses; this is faithful because both exist and the statements depend only on the law of the diffusion.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 2, (1.1); p. 3; p. 7, §1.4 (P_t)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `X` is the solution flow of `dX_t = b(X_t) dt + σ dB_t` driven by the path `B`: for every
starting point `x` and every `ω`, the path `t ↦ X x t ω` is continuous and
`X^x_t = x + ∫₀ᵗ b(X^x_s) ds + σ B_t` for all `t ≥ 0`. The noise is additive, so this is a
pathwise integral equation (no stochastic integral). -/
def IsSolution (b : E d → E d) (σ : Matrix (Fin d) (Fin d) ℝ)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) : Prop :=
  ∀ x ω, Continuous (fun t => X x t ω) ∧
    ∀ t : ℝ≥0, X x t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), b (X x s.toNNReal ω)) + mat σ (B t ω)

/-- `(P, B, X)` realizes the limiting diffusion (1.1) of the model `M`: `B` is a standard
`d`-dimensional Brownian motion under the probability measure `P`, and `X` is the solution
flow of `dX_t = g(X_t) dt + σ dB_t`. -/
def IsDiffusion (M : Model d) (P : Measure Ω) (B : ℝ≥0 → Ω → E d)
    (X : E d → ℝ≥0 → Ω → E d) : Prop :=
  IsProbabilityMeasure P ∧ EthierKurtz.IsStandardBrownian P B ∧ IsSolution M.g M.σ B X

/-- The Markov semigroup `P_t h(x) = E h(X^x_t)`. -/
noncomputable def semigroup (P : Measure Ω) (X : E d → ℝ≥0 → Ω → E d) (t : ℝ≥0)
    (h : E d → ℝ) (x : E d) : ℝ :=
  ∫ ω, h (X x t ω) ∂P

/-- `μ` is an invariant measure of `(P_t)`: `∫ P_t(x, A) μ(dx) = μ(A)` for every `t ≥ 0` and
every Borel set `A`, where `P_t(x, A) = P(X^x_t ∈ A)`. -/
def IsInvariant (P : Measure Ω) (X : E d → ℝ≥0 → Ω → E d) (μ : Measure (E d)) : Prop :=
  ∀ (t : ℝ≥0) (A : Set (E d)), MeasurableSet A → ∫⁻ x, P (X x t ⁻¹' A) ∂μ = μ A

end GPhNGIDiffusion.OccupationCLT


