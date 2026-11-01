-- Prove2me | Definitions.Def_DelayedGLCB_TailEnvelope
-- name    : DelayedGLCB_TailEnvelope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:29.310872+00:00
-- url     : https://prove2.me/theorems/954ec2b0-68c5-4f1d-a64a-e16604fd46d3
-- title:
--   Assumption 2: independent delays with a tail envelope $(\xi,\mu,M)$; $\sigma_G=\sigma\sqrt{2+q}$, $C_3=2\sigma^2+1$
-- statement:
--   Let $D_1,\dots,D_T$ be delays on a probability space with law $P$, let $\xi$ be a probability distribution, and let $\mu, M, q, \sigma$ be real numbers. The delays have **tail envelope** $(\xi,\mu,M)$ when:
--
--   1. $\xi$ is concentrated on $[0,\infty)$ and has finite mean $\mu=\int z\,\xi(dz)$;
--   2. for every $t\in[T]$ and every $m\ge M$, $P(D_t\ge m)\le\xi([m,\infty))$;
--   3. for every $x\ge0$,
--   $$
--   \xi\{z : z-\mu\ge x\}\le\exp\Big(-\frac{x^{1+q}}{2\sigma^2}\Big).
--   $$
--
--   The delays are **independent and non-negative** when $D_1,\dots,D_T$ are mutually independent random variables with $D_t\ge0$. Assumption 2 of the paper is the conjunction of both, with $M>0$ and $q\ge0$. The paper also writes $\sigma_G=\sigma\sqrt{2+q}$ and $C_3=2\sigma^2+1$.
--
--   The envelope lets the delays have different, unbounded distributions while controlling all their tails at once. At $q=0$ it covers exponential tails, at $q=1$ sub-Gaussian ones.
--
--   **Formalization Note** The paper only says "a distribution $\xi$ with mean $\mu<\infty$". Over all of $\mathbb R$ Proposition 1-1 is false ($\xi=\delta_{-100}$, $M=10$, $D_t\equiv9.5$), and $\xi$ is introduced as an envelope delay distribution, so $\xi$ lives on $[0,\infty)$. The tail inequality is required for $x\ge0$, where $x^{1+q}$ is a real power. Measurability of each $D_t$ is assumed. The constants $M>0$, $q\ge0$, $\sigma>0$ are separate hypotheses of each theorem.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Assumption 2, p.6; Proposition 1, p.8 (σ_G, C₃)

import Mathlib

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory

/-- **Tail-envelope distribution `(ξ, µ, M)` of the delays (Assumption 2 without independence).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Assumption 2 (Delay), p.6: "there exists a constant `M > 0`
and a distribution `ξ` with mean `µ < ∞` such that for any `m ≥ M` and `t ∈ [T]`,
`P(D_t ≥ m) ≤ P(D ≥ m)`, where `D ∼ ξ`. Furthermore, assume there exists `q ≥ 0` such that
`P(D − µ ≥ x) ≤ exp(−x^{1+q}/(2σ²))`, where `E[D] = µ`."

The constants `M > 0`, `q ≥ 0`, `σ > 0` are stated as separate hypotheses where the structure is used.

**Formalization Note.** (1) `ξ` is a probability measure on `[0, ∞)` (`ξ (−∞, 0) = 0`): the envelope
is a delay distribution (p.6, "an envelop distribution ξ uniformly dominating the tail probability of
all delays"); over all of `ℝ` Proposition 1-1 is false (`ξ = δ_{−100}`, `M = 10`, `D_t ≡ 9.5`). (2) "mean
`µ < ∞`" is integrability of the identity plus `∫ z dξ = µ`. (3) The tail inequality is required for
`x ≥ 0`, where `x^{1+q}` is the real power. -/
structure TailEnvelope {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ) (T : ℕ)
    (ξ : Measure ℝ) (μ M q σ : ℝ) : Prop where
  isProbability : IsProbabilityMeasure ξ
  nonneg : ξ (Set.Iio 0) = 0
  integrable : Integrable id ξ
  mean : ∫ z, z ∂ξ = μ
  dominated : ∀ t ∈ Finset.Icc 1 T, ∀ m : ℝ, M ≤ m → P {ω | m ≤ D t ω} ≤ ξ (Set.Ici m)
  tail : ∀ x : ℝ, 0 ≤ x →
    ξ {z | μ + x ≤ z} ≤ ENNReal.ofReal (Real.exp (-(x ^ (1 + q)) / (2 * σ ^ 2)))

/-- **Independent non-negative delays** `D_1, …, D_T` (Blanchet, Xu, Zhou, arXiv:2003.05174v1,
Assumption 2, p.6: "Assume `{D_t}_{t=1}^T` are independent non-negative random variables").

**Formalization Note.** Measurability of every `D_t` is the standing convention; non-negativity is
pointwise. Used in Proposition 1, which concerns the delays alone. -/
structure IndepDelays {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ) (T : ℕ) :
    Prop where
  measurable : ∀ t, Measurable (D t)
  nonneg : ∀ t ω, 0 ≤ D t ω
  indep : iIndepFun (fun t : Finset.Icc 1 T => D t) P

/-- `σ_G = σ√(2 + q)` (Blanchet, Xu, Zhou, arXiv:2003.05174v1, Proposition 1, p.8). -/
noncomputable def sigmaG (σ q : ℝ) : ℝ := σ * Real.sqrt (2 + q)

/-- `C₃ = 2σ² + 1` (Blanchet, Xu, Zhou, arXiv:2003.05174v1, Proposition 1-1, p.8). -/
noncomputable def C3 (σ : ℝ) : ℝ := 2 * σ ^ 2 + 1

end DelayedGLCB


