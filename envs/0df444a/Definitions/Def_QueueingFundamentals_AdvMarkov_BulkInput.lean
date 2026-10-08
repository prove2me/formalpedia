-- Prove2me | Definitions.Def_QueueingFundamentals_AdvMarkov_BulkInput
-- name    : QueueingFundamentals_AdvMarkov_BulkInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:22:37.657208+00:00
-- url     : https://prove2.me/theorems/90208ed3-a702-4b98-97a4-99e4025fcbd0
-- title:
--   The M^[X]/M/1 bulk-input queue: batch-size distributions, the balance equations (3.1), and generating functions
-- statement:
--   In the **$M^{[X]}/M/1$ bulk-input queue** of §3.1, customers arrive in batches at the epochs of a Poisson process with rate $\lambda$; the batch size $X$ has probabilities $c_n = \Pr\{X = n\}$, $n \ge 1$; a single server serves customers one at a time with exponential service at rate $\mu$. This module fixes four objects.
--
--   1. A **batch-size distribution**: a sequence $(c_n)_{n\ge 0}$ with $c_0 = 0$, $c_n \ge 0$ and $\sum_n c_n = 1$.
--   2. The **rate-balance equations** (3.1):
--   $$0 = -(\lambda+\mu)p_n + \mu p_{n+1} + \lambda\sum_{k=1}^{n} p_{n-k}c_k \quad (n \ge 1), \qquad 0 = -\lambda p_0 + \mu p_1.$$
--   3. A **steady-state solution**: a sequence $p_n \ge 0$ with $\sum_n p_n = 1$ that solves (3.1) (the book's convention, §1.9 and the footnote on p.118).
--   4. The **generating function** of a real sequence at a complex argument $z$,
--   $$P(z) = \sum_{n=0}^\infty p_n z^n, \qquad C(z) = \sum_{n=1}^\infty c_n z^n \quad (|z| \le 1).$$
--
--   **Formalization Note** The generating function is a `tsum` over $\mathbb C$; it is used only for $|z| \le 1$, where the series of a probability sequence converges absolutely. Because $c_0 = 0$, the generating function of $(c_n)_{n \ge 0}$ is the book's $C(z)$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.118, §3.1, Eq. (3.1) and the definitions of C(z) and P(z)

import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- A batch-size distribution (§3.1, p.118): probabilities `c_n = Pr{X = n}` of the number `X`
of customers in an arriving batch, supported on `{1, 2, …}` (`c_0 = 0`), nonnegative and
summing to one. -/
def IsBatchSizeDist (c : ℕ → ℝ) : Prop :=
  c 0 = 0 ∧ (∀ n : ℕ, 0 ≤ c n) ∧ HasSum c 1

/-- The rate-balance equations (3.1), p.118, of the `M^[X]/M/1` bulk-input queue with batch
arrival rate `λ`, service rate `μ` and batch-size probabilities `c_k`:
`0 = −(λ + μ)p_n + μp_{n+1} + λ ∑_{k=1}^{n} p_{n−k} c_k` for `n ≥ 1`, and `0 = −λp_0 + μp_1`. -/
def BulkInputBalance (lam mu : ℝ) (c p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      0 = -(lam + mu) * p n + mu * p (n + 1) + lam * ∑ k ∈ Finset.Icc 1 n, p (n - k) * c k) ∧
    0 = -lam * p 0 + mu * p 1

/-- A steady-state solution of the `M^[X]/M/1` queue (book convention, §1.9 p.34 and the footnote
on p.118): a probability distribution `{p_n}` on `{0, 1, 2, …}` that solves (3.1). -/
def IsBulkInputSteadyState (lam mu : ℝ) (c p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ BulkInputBalance lam mu c p

/-- The generating function `∑_{n ≥ 0} p_n zⁿ` of a real sequence at a complex argument `z`
(p.118: `C(z) = ∑_{n=1}^∞ c_n zⁿ` and `P(z) = ∑_{n=0}^∞ p_n zⁿ`, `|z| ≤ 1`). -/
noncomputable def cpgf (p : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (p n : ℂ) * z ^ n

end QueueingFundamentals.AdvMarkov


