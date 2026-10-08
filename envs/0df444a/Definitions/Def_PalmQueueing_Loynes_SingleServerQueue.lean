-- Prove2me | Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
-- name    : PalmQueueing_Loynes_SingleServerQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:41:39.655747+00:00
-- url     : https://prove2.me/theorems/dcbeafc5-2298-4daf-9e85-7f49cc22c0bd
-- title:
--   The G/G/1/∞ queue, the traffic intensity ρ, and Lindley's equation
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ carry a measurable flow $\{\theta_t\}$ with
--   $(P, \{\theta_t\})$ **ergodic**: $P$ is $\theta_t$-invariant, and every invariant event
--   ($\theta_t B = B$ for all $t$) is $P$-null or $P$-almost sure.
--
--   Let $A$ be a simple point process compatible with $\{\theta_t\}$, the **arrival process**, with
--   $T_n$ the arrival time of customer $n$, the conventions $T_n < T_{n+1}$ and $T_0 \le 0 < T_1$, and
--   finite intensity $\lambda = E[A((0,1])] < \infty$ (2.1.2). The inter-arrival times are
--   $$ \tau_n = T_{n+1} - T_n , \qquad n \in \mathbb{Z} . \tag{2.1.1} $$
--   Customer $n$ carries a required service $\sigma_n \ge 0$, and $\{\sigma_n\}$ is a sequence of
--   **marks** of the arrival process. With $P^0_A$ the Palm probability of $P$ and $A$, the **traffic
--   intensity** is
--   $$ \rho = \lambda E^0_A[\sigma_0] . \tag{2.1.3} $$
--   Equivalently $\rho = E^0_A[\sigma_0]/E^0_A[\tau_0]$ (2.1.5), and $P$-a.s.
--   $\rho = \lambda \lim_N N^{-1}\sum_{k=1}^N \sigma_k$ (2.1.4).
--
--   This $G/G$ input feeds a $G/G/1/\infty$ queue: one server at unit rate, infinite waiting room,
--   idle only when the system is empty. $W(t)$ denotes the amount of service remaining to be done at
--   time $t$; by convention a **workload process** is right-continuous with left-hand limits, and
--   between two successive arrivals it obeys **Lindley's equation**
--   $$ W(t) = \big(W(T_n-) + \sigma_n - (t - T_n)\big)^+ , \qquad t \in [T_n, T_{n+1}) . \tag{2.1.6} $$
--
--   Because a workload process is $\mathbb{R}$-valued here, "finite workload process" is carried by
--   the type — a process taking the value $+\infty$ is not one at all — which is what makes the
--   $\rho > 1$ half of Theorem 2.1.1 a genuine non-existence statement.
--
--   `loynesSet` is the set whose supremum is the Loynes variable (2.1.12),
--   $\{(T_n + \sum_{i=n}^{0}\sigma_i)^+ : n \le 0\}$. The book writes that sum as
--   $\sum_{i=0}^{n}$ with $n \le 0$, meaning the indices between $n$ and $0$; read the other way it is
--   empty.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §2.1.1-§2.1.2, pp. 76-78

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# The `G/G/1/∞` queue and its workload (§2.1, pp.76-78)

The data Theorem 2.1.1 is about: an ergodic flow, a stationary simple arrival process with its Palm
probability, service times carried as marks, the traffic intensity `ρ`, and what it means for a
process to be a workload process of the queue — Lindley's equation (2.1.6).

The vocabulary of Chapter 1 is imported rather than restated, so that the two missions cannot
drift apart: four of the five missions in this series need the same `Flow`, `PointProcess` and
`PalmSetting`.
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `G/G/1/∞` queue of §2.1.1 (pp.76-78): a `G/G` input `{(T_n, σ_n)}` fed to a single server
working at unit rate, on an ergodic flow. -/
structure Queue (Ω : Type*) [MeasurableSpace Ω] where
  /-- The arrival process `A = {T_n}` with its flow, `P`, `P⁰_A` and the intensity `λ` (2.1.2). -/
  toPalmSetting : PalmSetting Ω
  /-- The required service `σ_n ≥ 0` of customer `n`. -/
  sigma : ℤ → Ω → ℝ
  /-- Service times are non-negative. -/
  sigma_nonneg : ∀ (n : ℤ) (ω : Ω), 0 ≤ sigma n ω
  /-- `{σ_n}` is a sequence of marks of the arrival process (p.77). -/
  sigma_marks : IsMarkSequence toPalmSetting.θ toPalmSetting.N sigma
  /-- `(P, {θ_t})` is ergodic (p.76). -/
  ergodic : IsErgodicFlow toPalmSetting.θ toPalmSetting.P

/-- `(2.1.1)`: the inter-arrival time `τ_n = T_{n+1} − T_n`. -/
noncomputable def Queue.tau (Q : Queue Ω) (n : ℤ) (ω : Ω) : ℝ :=
  Q.toPalmSetting.N.T (n + 1) ω - Q.toPalmSetting.N.T n ω

/-- `(2.1.3)`: the **traffic intensity** `ρ = λ E⁰_A[σ₀]`. -/
noncomputable def Queue.rho (Q : Queue Ω) : ℝ :=
  Q.toPalmSetting.lam * ∫ ω, Q.sigma 0 ω ∂Q.toPalmSetting.P0

/-- `{W(t)}` is a **workload process** of the queue `Q`, with left-limit process `{Wl(t)}`.

By convention (p.78) a workload process is right-continuous with left-hand limits, and between two
successive arrivals it obeys **Lindley's equation**

`(2.1.6)  W(t) = (W(T_n−) + σ_n − (t − T_n))⁺,  t ∈ [T_n, T_{n+1})`.

Because `W` is `ℝ`-valued, "finite workload process" is carried by the type: a process taking the
value `+∞` is not of this type at all, which is what makes the `ρ > 1` half of Theorem 2.1.1 a
non-existence statement. -/
def IsWorkload (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ) : Prop :=
  (∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => W u ω) (Set.Ici s) s) ∧
  IsLeftLimitProcess W Wl ∧
  ∀ (n : ℤ) (ω : Ω) (t : ℝ),
    t ∈ Set.Ico (Q.toPalmSetting.N.T n ω) (Q.toPalmSetting.N.T (n + 1) ω) →
      W t ω = max (Wl (Q.toPalmSetting.N.T n ω) ω + Q.sigma n ω
        - (t - Q.toPalmSetting.N.T n ω)) 0

/-- The set whose supremum is the **Loynes variable** `(2.1.12)`:
`{ (T_n + Σ_{i=n}^{0} σ_i)⁺ : n ≤ 0 }`.

The book writes the sum as `Σ_{i=0}^{n}` with `n ≤ 0`, meaning the sum over the indices between
`n` and `0`; read the other way the formula is empty. Its content is the workload at the origin as
seen by looking back: the work brought by customers `n, …, 0` less the time `−T_n` that has since
elapsed, maximised over how far back one looks. -/
def loynesSet (Q : Queue Ω) (ω : Ω) : Set ℝ :=
  {x | ∃ n : ℤ, n ≤ 0 ∧
    x = max (Q.toPalmSetting.N.T n ω + ∑ i ∈ Finset.Icc n 0, Q.sigma i ω) 0}

end PalmQueueing.Loynes


