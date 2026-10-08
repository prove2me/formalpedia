-- Prove2me | Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess
-- name    : QueueingFundamentals_Foundations_ArrivalProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:35:03.592819+00:00
-- url     : https://prove2.me/theorems/2d3ada28-c281-4dc8-a47e-bdfbe0975410
-- title:
--   Arrival counting process with independent exponential interarrival times
-- statement:
--   Let $T_0,T_1,T_2,\dots$ be random variables on a probability space $(\Omega,\mathcal F,\mu)$ representing the times between successive arrivals. They are called *independent exponential interarrival times with rate* $\lambda$ if they are measurable, mutually independent, and each has the exponential distribution with rate $\lambda$ (mean $1/\lambda$), i.e. $\Pr\{T_i\le t\}=1-e^{-\lambda t}$ for $t\ge0$.
--
--   The $n$-th arrival epoch is the partial sum
--   $$S_n=T_0+T_1+\dots+T_{n-1}\qquad(S_0=0),$$
--   and the arrival counting process is
--   $$N(t)=\#\{n\ge1: S_n\le t\},$$
--   the number of arrivals in $[0,t]$.
--
--   This is the arrival process of §1.7 of the book, constructed from its interarrival times as on p.18, where $\Pr\{N(t)\le n\}=\Pr\{S_{n+1}>t\}$.
--
--   **Formalization Note** $N(t)$ is the cardinality of a set of indices; if that set were infinite Lean's `Set.ncard` would return $0$. For exponential interarrival times this happens only on an event of probability zero, so probabilities involving $N(t)$ are unaffected.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.16–18, §1.7 (arrival counting process N(t); interarrival time T, p.18)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- The interarrival times `T 0, T 1, T 2, …` (the book's `T`, "time between successive
arrivals", §1.7, p.18) are measurable, mutually independent, and each exponentially distributed
with rate `lam` (mean `1 / lam`) under the probability measure `μ`. -/
structure IsExpInterarrivals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (lam : ℝ)
    (T : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (T i)
  indep : iIndepFun T μ
  law : ∀ i, μ.map (T i) = expMeasure lam

/-- The `n`-th arrival epoch `T 0 + ⋯ + T (n-1)` (the sum of the first `n` interarrival times;
`0` for `n = 0`). -/
def arrivalTime {Ω : Type*} (T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, T i ω

/-- The arrival counting process `N(t)`: the number of arrivals in `[0, t]`, i.e. the number of
`n ≥ 1` whose `n`-th arrival epoch is at most `t` (so `N(0) = 0` when interarrival times are
positive). If infinitely many epochs are `≤ t`, `Set.ncard` returns `0`; for exponential
interarrival times this happens only on a null set. -/
noncomputable def countingProcess {Ω : Type*} (T : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.ncard

end QueueingFundamentals.Foundations


