-- Prove2me | Definitions.Def_QueueingFundamentals_AdvMarkov_BulkService
-- name    : QueueingFundamentals_AdvMarkov_BulkService
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:22:48.91524+00:00
-- url     : https://prove2.me/theorems/a27459d5-d15d-4975-acf7-f4abe5987fae
-- title:
--   The partial-batch M/M^[K]/1 bulk-service queue: balance equations (3.7) and steady-state solutions
-- statement:
--   In the **partial-batch bulk-service model** $M/M^{[K]}/1$ of §3.2.0.1, customers arrive one at a time at the epochs of a Poisson process with rate $\lambda$, and a single server serves up to $K$ customers at once; when fewer than $K$ are present the server takes them all, and later arrivals join the batch in service up to the limit $K$. A batch service lasts an exponential time with mean $1/\mu$, whatever its size. This module fixes two objects.
--
--   1. The **stochastic balance equations** (3.7):
--   $$0 = -(\lambda+\mu)p_n + \mu p_{n+K} + \lambda p_{n-1} \quad (n \ge 1), \qquad 0 = -\lambda p_0 + \mu p_1 + \mu p_2 + \cdots + \mu p_{K-1} + \mu p_K.$$
--   2. A **steady-state solution**: a sequence $p_n \ge 0$ with $\sum_n p_n = 1$ that solves (3.7) (the book's convention, §1.9 and the footnote on p.118).
--
--   **Formalization Note** The total mass is stated with `HasSum`, which also asserts convergence of the series.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.123–124, §3.2.0.1, Eq. (3.7)

import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- The stochastic balance equations (3.7), p.124, of the partial-batch `M/M^[K]/1` bulk-service
queue (§3.2.0.1): Poisson arrivals at rate `λ`, one server that serves up to `K` customers at a
time, exponential batch service at rate `μ`:
`0 = −(λ + μ)p_n + μp_{n+K} + λp_{n−1}` for `n ≥ 1`, and
`0 = −λp_0 + μp_1 + μp_2 + ⋯ + μp_{K−1} + μp_K`. -/
def PartialBatchBalance (lam mu : ℝ) (K : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 = -(lam + mu) * p n + mu * p (n + K) + lam * p (n - 1)) ∧
    0 = -lam * p 0 + mu * ∑ k ∈ Finset.Icc 1 K, p k

/-- A steady-state solution of the partial-batch `M/M^[K]/1` queue (book convention, §1.9 p.34
and the footnote on p.118): a probability distribution on `{0, 1, 2, …}` that solves (3.7). -/
def IsPartialBatchSteadyState (lam mu : ℝ) (K : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ PartialBatchBalance lam mu K p

end QueueingFundamentals.AdvMarkov


