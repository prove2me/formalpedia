-- Prove2me | Definitions.Def_ErlangA_Diffusion_Queue
-- name    : ErlangA_Diffusion_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:59.476968+00:00
-- url     : https://prove2.me/theorems/32d92808-0bd9-4ae1-bf31-78b5e4d5b128
-- title:
--   The Erlang-A ($M/M/N+M$) queue-length process via Poisson time changes, and its scaling $q_N = (Q_N - N)/\sqrt N$
-- statement:
--   This module defines the queue-length process of the $N$-th Erlang-A system of Garnett, Mandelbaum and Reiman (2002) and its centred, rescaled version.
--
--   **The model** (§1, pp. 209–210). Callers arrive as a Poisson process of rate $\lambda$. There are $N$ statistically identical agents, each serving at exponential rate $\mu$, and an unlimited waiting room served first come, first served. Each caller has an exponential patience of rate $\theta$; a caller whose wait in queue exceeds the patience abandons. The number of callers in the system $Q(t)$ is then a birth–death process with birth rate $\lambda$ in every state and death rate $\min(k,N)\mu + (k-N)^+\theta$ in state $k$.
--
--   **The Erlang-A system.** On a probability space $(\Omega, \mathcal F, P)$, let $A$, $S$, $R$ be unit-rate Poisson processes. A process $Q$ with values in $\{0, 1, 2, \dots\}$ is the queue-length process of the $N$-th Erlang-A system with rates $(\lambda, \mu, \theta)$ if
--
--   1. $A$, $S$, $R$ (as paths on $[0,\infty)$) and the initial value $Q(0)$ are mutually independent;
--   2. every path of $Q$ is right-continuous with left limits on $[0,\infty)$ and every $Q(t)$ is a random variable;
--   3. almost surely, for every $t \ge 0$,
--   $$
--   Q(t) = Q(0) + A(\lambda t) - S\Big(\mu\int_0^t \min(Q(s), N)\,ds\Big) - R\Big(\theta \int_0^t (Q(s) - N)^+\,ds\Big).
--   $$
--
--   **Scaling** (p. 216). The centred and rescaled process is
--   $$
--   q_N(t) = \frac{Q_N(t) - N}{\sqrt N}.
--   $$
--   Its absolute value is the queue length when $q_N \ge 0$ and the number of idle agents when $q_N \le 0$.
--
--   **Traffic intensity** (p. 215). $\rho_N = \lambda_N/(N\mu)$.
--
--   **Formalization Note** The paper says only that $Q$ is a birth–death process (p. 211). The time-change representation above is the construction of Mandelbaum, Massey and Reiman (1998), which the paper cites (p. 212); it determines $Q$ pathwise, jump by jump, and the resulting process has the birth–death law above. The Poisson processes are `ManyServerQED.Scheduling.IsPoissonProcess` with rate $1$; path regularity is `BellWilliams2001.ThresholdPolicy.IsCadlag`. Time is real and every condition is imposed for $t \ge 0$ only. $q_N$ is valued in $\mathbb R^1$ (`Fin 1 → ℝ`) to match the path-space convergence notion used in Theorem 2.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, pp. 209–210, §1 (model); p. 215, §4 (ρ_N); p. 216 (q_N)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ErlangA.Diffusion

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling

/-!
Garnett, Mandelbaum & Reiman (2002), §1 (pp. 209–210) and §4 (pp. 215–216): the Erlang-A
(`M/M/N + M`) queue-length process of the `N`-th system and its centred, `√N`-scaled version.

Conventions. Time is real and every condition quantifies over `t ≥ 0` (as in
`BellWilliams2001.ThresholdPolicy.Paths`). The queue-length process is realized through the
time-change representation of Mandelbaum, Massey & Reiman (1998), cited by the paper on p. 212.
-/

/-- **The `N`-th Erlang-A system.** On `(Ω, P)`, `Q : Ω → ℝ → ℕ` is the number of callers in an
`M/M/N + M` queue with `N` agents, arrival rate `λ`, service rate `μ` per agent and patience
rate `θ`, built from three unit-rate Poisson processes `A` (arrivals), `S` (services) and `R`
(abandonments):
* `P` is a probability measure; `A`, `S`, `R` are Poisson processes of rate `1`;
* `A`, `S`, `R` (their paths on `t ≥ 0`) and the initial value `Q(0)` are mutually independent;
* every path of `Q` is right-continuous with left limits on `[0, ∞)`, and every `Q(t)` is a
  random variable;
* the integrands below are integrable on every `[0, t]`;
* almost surely, for every `t ≥ 0`,
  `Q(t) = Q(0) + A(λt) − S(μ ∫₀ᵗ min(Q(s), N) ds) − R(θ ∫₀ᵗ (Q(s) − N)⁺ ds)`.

The resulting `Q` is a birth–death process with birth rate `λ` and death rate
`min(k, N) μ + (k − N)⁺ θ` in state `k`, started from `Q(0)`. -/
structure IsErlangASystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (lam μ θ : ℝ) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ) : Prop where
  isProb : IsProbabilityMeasure P
  poisson_A : IsPoissonProcess P A 1
  poisson_S : IsPoissonProcess P S 1
  poisson_R : IsPoissonProcess P R 1
  indep : iIndepFun (![fun ω (t : ℝ≥0) => A ω t, fun ω (t : ℝ≥0) => S ω t,
    fun ω (t : ℝ≥0) => R ω t, fun ω (_ : ℝ≥0) => (Q ω 0 : ℝ)] : Fin 4 → Ω → ℝ≥0 → ℝ) P
  cadlag : ∀ ω, IsCadlag (fun t => (Q ω t : ℝ))
  meas : ∀ t, Measurable (fun ω => Q ω t)
  integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntervalIntegrable (fun s => min ((Q ω s : ℝ)) (N : ℝ)) volume 0 t ∧
    IntervalIntegrable (fun s => max ((Q ω s : ℝ) - N) 0) volume 0 t
  eqn : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (Q ω t : ℝ) = (Q ω 0 : ℝ) + A ω (lam * t)
      - S ω (μ * ∫ s in (0 : ℝ)..t, min ((Q ω s : ℝ)) (N : ℝ))
      - R ω (θ * ∫ s in (0 : ℝ)..t, max ((Q ω s : ℝ) - N) 0)

/-- The centred and rescaled process `q_N(t) = (Q_N(t) − N)/√N` (p. 216), as an `ℝ¹`-valued
process (the shape used by `BellWilliams2001.ThresholdPolicy.CouplingConverges`). -/
noncomputable def scaled {Ω : Type*} (N : ℕ) (Q : Ω → ℝ → ℕ) : Ω → ℝ → Fin 1 → ℝ :=
  fun ω t _ => ((Q ω t : ℝ) - N) / Real.sqrt N

/-- Traffic intensity `ρ_N = λ_N/(Nμ)` of the `N`-th system (p. 215). -/
noncomputable def trafficIntensity (lam : ℕ → ℝ) (μ : ℝ) (N : ℕ) : ℝ :=
  lam N / (N * μ)

end ErlangA.Diffusion


