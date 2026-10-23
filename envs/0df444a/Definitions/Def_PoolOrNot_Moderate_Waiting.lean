-- Prove2me | Definitions.Def_PoolOrNot_Moderate_Waiting
-- name    : PoolOrNot_Moderate_Waiting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:46.738206+00:00
-- url     : https://prove2.me/theorems/df2db247-7294-4ed7-ba64-746d5a350e79
-- title:
--   §5.1, p. 9 — T_a(i), the PWT laws Wⁿ_D and Wⁿ_P, and the performance measures P(De), P(Ab), E[W], E[V], Var(W)
-- statement:
--   Waiting-time objects for the dedicated (DQ–JSQ) and pooled (M/M/n+M) designs.
--
--   1. **Absorption times.** $T_a(0) = 0$ and, for $i \ge 1$, $T_a(i) = \sum_{k=0}^{i-1} \xi_{i,k}$ with independent $\xi_{i,k}$ exponential of rate $\mu + k\theta$: the time to absorption of the pure death process with death rate $\mu + \theta(j-1)$ in state $j$, started from $i$. More generally, $\mathrm{Hypo}(a_0, \dots, a_{k-1})$ is the law of a sum of independent exponentials with rates $a_0, \dots, a_{k-1}$.
--
--   2. **PWT of the DQ–JSQ system.** If $\pi$ is a stationary law of the $n$-server DQ–JSQ chain, the steady-state potential waiting time $W^n_D$ has law
--   $$\mathcal L(W^n_D) = \sum_{i \ge 0} \pi\{\text{an arrival joins a server with exactly } i \text{ customers}\}\;\mathcal L(T_a(i)).$$
--
--   3. **PWT of the M/M/n+M system.** With $\pi_k$ the stationary distribution of the number in an M/M/n+M system with arrival rate $\lambda$,
--   $$\mathcal L(W^n_P) = \Bigl(\sum_{k<n} \pi_k\Bigr)\delta_0 + \sum_{m \ge 0} \pi_{n+m}\,\mathrm{Hypo}(n\mu, n\mu + \theta, \dots, n\mu + m\theta).$$
--
--   4. **Performance measures** of a PWT $W$, with a patience time $R$ exponential of rate $\theta$ independent of $W$ and the actual waiting time $V = W \wedge R$: $P(\mathrm{De}) = P(W > 0)$, $E[W]$, $E[W \mid W > 0]$, $\mathrm{Var}(W)$, $P(\mathrm{Ab}) = P(R < W)$, $E[V]$, $E[V \mid W \le R]$, $E[V \mid W > R]$; and the mean fluid-scaled number in system, $E[X/n]$ with $X = \sum_{i \ge 1} Q_i$ for the DQ–JSQ system and $X = \sum_k k\pi_k$ for M/M/n+M.
--
--   These are the quantities compared in Theorem 5.
--
--   **Formalization Note** Laws are measures on $\mathbb R$; sums of independent variables are additive convolutions of `ProbabilityTheory.expMeasure`. The DQ–JSQ PWT law is a definition that combines PASTA with the page's sentence "If a customer joins a server having $i$ customers, the PWT will have the same distribution as $T_a(i)$"; the arrival-seen probabilities are `prob π (ArrivesAt · i)` on the published state space (0-based). The M/M/n+M stationary law is the published `ErlangA.Abandonment.stationaryDist`. Conditional means are ratios; Lean's $x/0 = 0$ applies only when the conditioning event has probability $0$. `variance` is Mathlib's `ProbabilityTheory.variance id W`, whose value is $0$ when $W$ has no finite second moment; statements that use it also assert the second moment is finite.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, pp. 6, 9–10 (PDF 7, 10–11), X(t) before (10), §5.1 (T_a(i), Wⁿ, Vⁿ), §5.2 (PQ comparison system)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_ErlangA_Abandonment_Model

open MeasureTheory ProbabilityTheory JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

open scoped Classical

/-- The law of a sum of `k` independent exponential random variables with rates
`rate 0, …, rate (k − 1)`: `hypoLaw rate 0 = δ_0` and
`hypoLaw rate (k+1) = hypoLaw rate k ∗ Exp(rate k)` (additive convolution). -/
noncomputable def hypoLaw (rate : ℕ → ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (hypoLaw rate k) (expMeasure (rate k))

/-- The law of `T_a(i) = Σ_{k=0}^{i−1} ξ_{i,k}` (§5.1, p. 9), the time to absorption of the pure
death process with death rate `μ + θ(j − 1)` in state `j` started from `i`: the `ξ_{i,k}` are
independent exponentials with means `1/(μ + kθ)`. `taLaw μ θ 0 = δ_0` (`T_a(0) = 0`). -/
noncomputable def taLaw (μ θ : ℝ) (i : ℕ) : Measure ℝ :=
  hypoLaw (fun k => μ + (k : ℝ) * θ) i

/-- The law of the steady-state potential waiting time `Wⁿ_D` of the `n`-server DQ–JSQ system
(§5.1, p. 9) whose augmented queue length has stationary law `π`: by PASTA an arrival sees `π`,
joins (JSQ) a server with exactly `i` customers with probability `π{ArrivesAt · i}`, and then waits
a time distributed as `T_a(i)`. -/
noncomputable def pwtLawD {n : ℕ} (π : State n → ℝ) (μ θ : ℝ) : Measure ℝ :=
  Measure.sum (fun i : ℕ => ENNReal.ofReal (prob π (fun q => ArrivesAt q i)) • taLaw μ θ i)

/-- The law of the steady-state potential waiting time `Wⁿ_P` of the `M/M/n + M` (pooled) system
with total arrival rate `lam`, service rate `μ`, patience rate `θ` and stationary law
`π_k = ErlangA.Abandonment.stationaryDist n lam μ θ k`: an arrival finding `k < n` customers waits
`0`; one finding `n + m` customers waits a sum of `m + 1` independent exponentials with rates
`nμ + jθ`, `j = 0, …, m`. -/
noncomputable def pwtLawP (n : ℕ) (lam μ θ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (∑ k ∈ Finset.range n, ErlangA.Abandonment.stationaryDist n lam μ θ k) •
      Measure.dirac 0 +
    Measure.sum (fun m : ℕ =>
      ENNReal.ofReal (ErlangA.Abandonment.stationaryDist n lam μ θ (n + m)) •
        hypoLaw (fun j => (n : ℝ) * μ + (j : ℝ) * θ) (m + 1))

/-- `P(De) = P(W > 0)`, the probability of delay, for a PWT law `W`. -/
noncomputable def probDelay (W : Measure ℝ) : ℝ :=
  (W (Set.Ioi 0)).toReal

/-- `E[W]`, the mean PWT. -/
noncomputable def meanPWT (W : Measure ℝ) : ℝ :=
  ∫ w, w ∂W

/-- `E[W | W > 0] = E[W; W > 0] / P(W > 0)`, the mean PWT of delayed customers. -/
noncomputable def meanPWTDelayed (W : Measure ℝ) : ℝ :=
  (∫ w in Set.Ioi 0, w ∂W) / probDelay W

/-- `Var(W)`, the variance of the PWT. -/
noncomputable def varPWT (W : Measure ℝ) : ℝ :=
  variance id W

/-- The joint law of `(W, R)`: PWT `W` and an independent exponential patience `R` of rate `θ`. -/
noncomputable def jointLaw (W : Measure ℝ) (θ : ℝ) : Measure (ℝ × ℝ) :=
  W.prod (expMeasure θ)

/-- `P(Ab) = P(R < W)`, the probability of abandonment. -/
noncomputable def probAb (W : Measure ℝ) (θ : ℝ) : ℝ :=
  (jointLaw W θ {p | p.2 < p.1}).toReal

/-- `E[V]` with `V = W ∧ R`, the mean actual waiting time (AWT). -/
noncomputable def meanAWT (W : Measure ℝ) (θ : ℝ) : ℝ :=
  ∫ p, min p.1 p.2 ∂(jointLaw W θ)

/-- `E[V | W ≤ R]`, the mean AWT of served customers. -/
noncomputable def meanAWTServed (W : Measure ℝ) (θ : ℝ) : ℝ :=
  (∫ p in {p : ℝ × ℝ | p.1 ≤ p.2}, min p.1 p.2 ∂(jointLaw W θ)) /
    (jointLaw W θ {p | p.1 ≤ p.2}).toReal

/-- `E[V | W > R]`, the mean AWT of abandoning customers. -/
noncomputable def meanAWTAband (W : Measure ℝ) (θ : ℝ) : ℝ :=
  (∫ p in {p : ℝ × ℝ | p.2 < p.1}, min p.1 p.2 ∂(jointLaw W θ)) /
    (jointLaw W θ {p | p.2 < p.1}).toReal

/-- `E[X̄ⁿ_D(∞)]`: the mean fluid-scaled number of customers `X/n = (Σ_{i≥1} Q_i)/n` (p. 6) of the
DQ–JSQ system under the stationary law `π`. -/
noncomputable def meanOccD {n : ℕ} (π : State n → ℝ) : ℝ :=
  expect π (fun q => (∑' i : ℕ, (q.1 i : ℝ)) / (n : ℝ))

/-- `E[X̄ⁿ_P(∞)]`: the mean fluid-scaled number of customers `(Σ_k k π_k)/n` of the `M/M/n + M`
system. -/
noncomputable def meanOccP (n : ℕ) (lam μ θ : ℝ) : ℝ :=
  (∑' k : ℕ, (k : ℝ) * ErlangA.Abandonment.stationaryDist n lam μ θ k) / (n : ℝ)

end PoolOrNot.Moderate


