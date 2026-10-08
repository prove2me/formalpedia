-- Prove2me | Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
-- name    : QueueingFundamentals_GM1_EmbeddedChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:51:41.865452+00:00
-- url     : https://prove2.me/theorems/e4f3260e-1817-493f-806c-8f2948fdc899
-- title:
--   The G/M/1 arrival-point Markov chain, $b_k$, and $\beta(z)$
-- statement:
--   This file sets up the single-server G/M/1 queue of §5.3.1: interarrival times are independent and identically distributed with CDF $A(t)$, and service times are exponential with rate $\mu > 0$.
--
--   1. **Interarrival law.** $A$ is a probability measure on $\mathbb R$ carried by $[0,\infty)$, with finite mean $E[T] = 1/\lambda$.
--   2. **Service completions per interarrival time** (Eq. (5.50)). For $k \ge 0$,
--   $$
--   b_k = \int_0^\infty \frac{e^{-\mu t}(\mu t)^k}{k!}\,dA(t),
--   $$
--   the probability of exactly $k$ service completions during an interarrival time when enough customers are present.
--   3. **Transition matrix** (Eq. (5.51)). The number $X_n$ in the system just before the $n$th arrival is a Markov chain with transition probabilities
--   $$
--   p_{i0} = 1 - \sum_{k=0}^{i} b_k, \qquad p_{ij} = b_{i+1-j}\ (1 \le j \le i+1), \qquad p_{ij} = 0\ (j > i+1).
--   $$
--   4. **Stationary arrival-point vector** (Eq. (5.52)). A sequence $q = \{q_n\}_{n\ge0}$ is stationary when $q_n \ge 0$, $\sum_n q_n = 1$ ($qe = 1$), and $\sum_i q_i p_{ij} = q_j$ for every $j$ ($qP = q$); $q_n$ is the probability that an arrival finds $n$ in the system.
--   5. **Generating function** (Eq. (5.55)). $\beta(z) = \sum_{n\ge0} b_n z^n$ for complex $z$.
--   6. **Laplace–Stieltjes transform.** $A^*(s) = \int_0^\infty e^{-sx}\,dA(x)$ for complex $s$.
--
--   These objects carry every result of the chapter's G/M/1 analysis: the characteristic equation $z = \beta(z)$, its root $r_0$, and the geometric arrival-point law.
--
--   **Formalization Note** $b_k$ and $A^*$ are integrals over $[0,\infty)$ (closed at $0$, so an atom of $A$ at $0$ is counted, as in the Stieltjes integral). $\beta$ is a `tsum`, which Lean sets to $0$ where the series diverges; every theorem using $\beta$ evaluates it only where $|z| \le 1$, where it converges absolutely. The rate $\lambda > 0$ is a separate hypothesis of each theorem.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.259–261, Eqs. (5.50), (5.51), (5.52), (5.55) and the LST A*(z) of (5.56), §5.3.1

import Mathlib

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- The interarrival-time law of the G/M/1 queue (§5.3.1, p.259): a probability measure `A` on `ℝ`
(the law of the interarrival time `T`, with CDF `A(t)`), carried by `[0, ∞)`, with finite mean
`E[T] = 1/λ`. -/
structure IsInterarrivalLaw (A : Measure ℝ) (lam : ℝ) : Prop where
  isProbability : IsProbabilityMeasure A
  nonneg : A (Set.Iio 0) = 0
  integrable : Integrable (fun x : ℝ => x) A
  mean : ∫ x, x ∂A = 1 / lam

/-- Eq. (5.50): `b_k = ∫_0^∞ e^{-μt} (μt)^k / k! dA(t)`, the probability of exactly `k` exponential
(rate `μ`) service completions during an interarrival time. -/
noncomputable def serviceProb (A : Measure ℝ) (mu : ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), Real.exp (-mu * t) * (mu * t) ^ k / (Nat.factorial k : ℝ) ∂A

/-- Eq. (5.51): the one-step transition probabilities `p_{ij}` of the arrival-point chain
`X_{n+1} = X_n + 1 - B_n`:
`p_{i0} = 1 - ∑_{k=0}^{i} b_k`, `p_{ij} = b_{i+1-j}` for `1 ≤ j ≤ i + 1`, and `p_{ij} = 0` for
`j > i + 1`. -/
noncomputable def transitionProb (A : Measure ℝ) (mu : ℝ) (i j : ℕ) : ℝ :=
  if j = 0 then 1 - ∑ k ∈ Finset.range (i + 1), serviceProb A mu k
  else if j ≤ i + 1 then serviceProb A mu (i + 1 - j)
  else 0

/-- Eq. (5.52): `q = {q_n}` is a stationary probability vector of the arrival-point chain, i.e.
`q ≥ 0`, `qe = 1` and `qP = q` (each `(qP)_j = ∑_i q_i p_{ij}` a convergent series equal to `q_j`). -/
def IsArrivalPointStationary (A : Measure ℝ) (mu : ℝ) (q : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ q n) ∧ HasSum q 1 ∧
    ∀ j, HasSum (fun i => q i * transitionProb A mu i j) (q j)

/-- Eq. (5.55): the probability generating function `β(z) = ∑_{n ≥ 0} b_n z^n` of `{b_n}`, at a
complex argument `z`. -/
noncomputable def beta (A : Measure ℝ) (mu : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (serviceProb A mu n : ℂ) * z ^ n

/-- The Laplace–Stieltjes transform `A*(s) = ∫_0^∞ e^{-sx} dA(x)` of the interarrival-time CDF, at a
complex argument `s`. -/
noncomputable def lst (A : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ici (0 : ℝ), Complex.exp (-s * (x : ℂ)) ∂A

end QueueingFundamentals.GM1


