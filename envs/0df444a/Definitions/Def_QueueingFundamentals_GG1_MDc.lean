-- Prove2me | Definitions.Def_QueueingFundamentals_GG1_MDc
-- name    : QueueingFundamentals_GG1_MDc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T19:34:43.186758+00:00
-- url     : https://prove2.me/theorems/21605411-8ae4-46fb-8d64-86fc1dd09d9c
-- title:
--   The M/D/c steady-state equations (6.17) and the generating function P(z)
-- statement:
--   Consider the M/D/c queue: $c$ servers, Poisson arrivals, and a constant service time, which is taken as the unit of time, so that $\lambda$ is the mean number of arrivals per service time. Write
--
--   $$
--   a_m=\frac{\lambda^m e^{-\lambda}}{m!}\qquad(m=0,1,2,\dots)
--   $$
--
--   for the probability of $m$ arrivals in one unit of time, and for a sequence $(p_n)_{n\ge0}$ let $P_c=\sum_{n=0}^{c}p_n$ ("$c$ or less in system"). The steady-state equations (6.17) are
--
--   $$
--   p_n=P_c\,a_n+p_{c+1}a_{n-1}+\cdots+p_{c+n}a_0=P_c\,a_n+\sum_{k=1}^{n}p_{c+k}\,a_{n-k}\qquad(n\ge0),
--   $$
--
--   and a **steady-state distribution** is a sequence with $p_n\ge0$, $\sum_n p_n=1$ solving them. Its generating function is $P(z)=\sum_{n=0}^{\infty}p_nz^n$ for complex $z$.
--
--   The equations express that the system observed at the ends of successive unit service intervals is a Markov chain: whoever is in service at the start of an interval has left by its end.
--
--   **Formalization Note** The arrival rate is `lam` because `λ` is a Lean keyword. The index $n-k$ is a natural-number subtraction used only for $k\le n$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.294–295, §6.3, Eq. (6.17) and the generating function P(z) of p.295

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

namespace QueueingFundamentals.GG1

/-- The Poisson probability `λ^n e^{−λ}/n!` of `n` arrivals in one unit of time (the constant
service time of the M/D/c queue, §6.3, p.294). The arrival rate is `lam` (`λ` is a Lean keyword). -/
noncomputable def poissonProb (lam : ℝ) (n : ℕ) : ℝ :=
  lam ^ n * Real.exp (-lam) / (Nat.factorial n : ℝ)

/-- `P_c = ∑_{n=0}^{c} p_n`, the probability of `c` or fewer in the system (p.295). -/
def cumProb (p : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), p n

/-- The M/D/c steady-state equations (6.17) (p.295), with the service time as the unit of time:
for every `n ≥ 0`,
`p_n = P_c λ^n e^{−λ}/n! + p_{c+1} λ^{n−1} e^{−λ}/(n−1)! + ⋯ + p_{c+n} e^{−λ}`,
i.e. `p_n = P_c·a_n + ∑_{k=1}^{n} p_{c+k} a_{n−k}` with `a_m = λ^m e^{−λ}/m!`
(`n − k` is never truncated since `k ≤ n`). -/
def MDcBalance (lam : ℝ) (c : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, p n = cumProb p c * poissonProb lam n +
    ∑ k ∈ Finset.Icc 1 n, p (c + k) * poissonProb lam (n - k)

/-- `p` is a steady-state distribution of the M/D/c queue with arrival rate `lam` (per unit
service time): a probability vector on `{0, 1, 2, …}` solving (6.17). -/
def IsMDcStationary (lam : ℝ) (c : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ HasSum p 1 ∧ MDcBalance lam c p

end QueueingFundamentals.GG1


