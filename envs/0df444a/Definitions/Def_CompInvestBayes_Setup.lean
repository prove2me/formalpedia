-- Prove2me | Definitions.Def_CompInvestBayes_Setup
-- name    : CompInvestBayes_Setup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:58.779059+00:00
-- url     : https://prove2.me/theorems/0b93115d-7a36-4c15-ad1d-f74eda91b460
-- title:
--   Probability space with independent Brownian motions $B^s_1, B_1, B_2$ and a uniform variable
-- statement:
--   The model lives on a probability space $(\Omega,\mathcal F,\mathbb P)$ carrying three standard real Brownian motions $B^s_1$, $B_1$, $B_2$, indexed by time $t\ge 0$, and a random variable $U$ uniformly distributed on $[0,1]$, the four being mutually independent. $B^s_1$ drives the leader's earnings before the follower enters, $B_1$ the leader's earnings after entry, and $B_2$ the follower's earnings.
--
--   For a prior belief $y_0\in[0,1]$ the market state is $\theta := \mathbf 1\{U<y_0\}$, so that $\mathbb P(\theta=1)=y_0$ and $\theta$ is independent of the Brownian motions, as in the paper's model.
--
--   **Formalization Note** Realizing $\theta$ from $U$ puts every prior $y_0$ on one space, which is needed to differentiate the leader's equilibrium value in $y_0$. The Brownian motions satisfy Mathlib's `IsBrownianReal` (unit variance; the volatility $\sigma$ multiplies them in the earning processes), every $B_t$ is measurable, and every path is continuous (a continuous modification).
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), §2, p.7 (PDF 7), the probability space (Ω, F, P) with independent standard Brownian motions and the binary θ

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

/-- **The probability space** of the model (SSRN 3408260, §2, p.7, PDF 7): "we take a probability
space (Ω, F, P) such that independent standard Brownian motions Bs1, B1 and B2, and a binary random
variable θ independent of these Brownian motions are defined on this space."

Fields: the probability measure `P`; three standard real Brownian motions `Bs` (the noise of the
leader's earnings before entry, `B^s_1` in (1)), `B1` (leader after entry, (3)) and `B2` (follower,
(4)), indexed by `t ∈ ℝ≥0`; and a random variable `U`, uniform on `[0, 1]`. The four objects
`Bs`, `B1`, `B2` (as path-valued random variables) and `U` are mutually independent.

**Formalization Note.**
* The binary market state is realized from `U` as `θ = 1{U < y₀}` (see `favorable`), so that
  `P(θ = 1) = y₀` and `θ` is independent of the Brownian motions **for every prior `y₀ ∈ [0, 1]` on one
  space**. The leader's equilibrium value is then a function of `y₀` on a single space, which its
  derivative in `y₀` (Theorem 4) needs.
* Brownian motions are Mathlib's `IsBrownianReal` (unit variance; the volatility `σ` multiplies the
  Brownian motion in the earning processes). Every `B t` is measurable and **every** path is
  continuous: a continuous modification, which `IsBrownianReal` provides almost surely. -/
structure Setup (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability measure -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  /-- pre-entry noise of the leader, `B^s_1` -/
  Bs : ℝ≥0 → Ω → ℝ
  /-- post-entry noise of the leader, `B_1` -/
  B1 : ℝ≥0 → Ω → ℝ
  /-- noise of the follower, `B_2` -/
  B2 : ℝ≥0 → Ω → ℝ
  /-- uniform variable realizing the market state `θ` -/
  U : Ω → ℝ
  brownian_Bs : IsBrownianReal Bs P
  brownian_B1 : IsBrownianReal B1 P
  brownian_B2 : IsBrownianReal B2 P
  measurable_Bs : ∀ t, Measurable (Bs t)
  measurable_B1 : ∀ t, Measurable (B1 t)
  measurable_B2 : ∀ t, Measurable (B2 t)
  continuous_Bs : ∀ ω, Continuous (fun t => Bs t ω)
  continuous_B1 : ∀ ω, Continuous (fun t => B1 t ω)
  continuous_B2 : ∀ ω, Continuous (fun t => B2 t ω)
  measurable_U : Measurable U
  uniform_U : HasLaw U (volume.restrict (Set.Icc (0 : ℝ) 1)) P
  /-- `Bs`, `B1`, `B2` and `U` are mutually independent. -/
  indep : iIndep
    ![MeasurableSpace.comap (fun ω (t : ℝ≥0) => Bs t ω) MeasurableSpace.pi,
      MeasurableSpace.comap (fun ω (t : ℝ≥0) => B1 t ω) MeasurableSpace.pi,
      MeasurableSpace.comap (fun ω (t : ℝ≥0) => B2 t ω) MeasurableSpace.pi,
      MeasurableSpace.comap U inferInstance] P

end CompInvestBayes


