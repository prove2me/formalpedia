-- Prove2me | Definitions.Def_SeqExpDiffusion_IsBeliefDiffusion
-- name    : SeqExpDiffusion_IsBeliefDiffusion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:02.39464+00:00
-- url     : https://prove2.me/theorems/c1ae92c2-5705-4e05-9b0a-48c24235924d
-- title:
--   The belief diffusion $d\tilde\delta_t=\tilde\sigma\tilde\delta_t(1-\tilde\delta_t)\,dW_t$
-- statement:
--   Fix $\tilde\sigma\in\mathbb R$ and an initial belief $\delta_0$. A process $(\tilde\delta_t)_{t\ge0}$ on a probability space $(\Omega,P)$ with filtration $(\mathcal F_t)$ is a **belief diffusion started at $\delta_0$** if there is a standard Brownian motion $W$ with respect to $(\mathcal F_t)$ (adapted, with increments independent of the past) such that $\tilde\delta$ is adapted, has continuous paths with values in $[0,1]$, and solves
--
--   $$d\tilde\delta_t=\tilde\sigma\,\tilde\delta_t(1-\tilde\delta_t)\,dW_t,\qquad \tilde\delta_0=\delta_0,$$
--
--   that is, for every $t$, almost surely $\tilde\delta_t=\delta_0+\int_0^t\tilde\sigma\,\tilde\delta_s(1-\tilde\delta_s)\,dW_s$.
--
--   This is the diffusion limit of the posterior belief under the optimal experiment, and the state process of the stopping problem (12).
--
--   **Formalization Note** The stochastic integral is the published relation `EthierKurtz.HasBrownianItoIntegral` (predictable dyadic step approximations, convergence in probability). Paths are continuous and in $[0,1]$ for every $\omega$. The filtration is any filtration for which $W$ is Brownian, in the sense of the published general definition `EllsbergLearning.IsBrownianWrt`; the paper's filtration of the experimentation history is one of them.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (12), p.17

import Mathlib
import Definitions.Def_EllsbergLearning_IsBrownianWrt
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SeqExpDiffusion

/-- `X` is the belief diffusion of (12) started at `δ₀`:
`dδ̃_t = σ̃ δ̃_t (1 − δ̃_t) dW_t`, `δ̃_0 = δ₀`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (12), p.17.

The data are a probability space `(Ω, P)`, a filtration `ℱ`, an `ℱ`-Brownian motion `B` (the
paper's `W`) and an `ℱ`-adapted process `X` with continuous paths in `[0, 1]`, such that for each
`t`, almost surely, `X t = δ₀ + ∫₀ᵗ σ X_s (1 − X_s) dB_s`.

**Formalization Note** The stochastic integral is the published relation
`EthierKurtz.HasBrownianItoIntegral` (predictable dyadic step approximations, convergence in
probability). Paths are continuous and valued in `[0, 1]` for every `ω`, not only almost surely.
The filtration is any filtration for which `B` is Brownian (the published general notion
`EllsbergLearning.IsBrownianWrt`); the paper's `𝔽` (p.8) is one of them. -/
structure IsBeliefDiffusion {Ω : Type*} {mΩ : MeasurableSpace Ω} (σ δ₀ : ℝ) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (B X : ℝ≥0 → Ω → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  brownian : EllsbergLearning.IsBrownianWrt ℱ P B
  adapted : Adapted ℱ X
  continuous : ∀ ω, Continuous fun t => X t ω
  mem_Icc : ∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1
  initial : ∀ᵐ ω ∂P, X 0 ω = δ₀
  ito : ∃ J : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (fun t => ℱ t) B
      (fun t ω => σ * X t ω * (1 - X t ω)) J ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X t ω = δ₀ + J t ω

end SeqExpDiffusion


