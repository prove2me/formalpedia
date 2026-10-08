-- Prove2me | Definitions.Def_QueueingFundamentals_BirthDeath_Balance
-- name    : QueueingFundamentals_BirthDeath_Balance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:01:27.401869+00:00
-- url     : https://prove2.me/theorems/06c5124e-0c19-49dc-bb87-1726bc444f9b
-- title:
--   Birth–death processes: balance equations, steady-state solutions and the M/M/c, M/M/c/K, M/M/∞ rates
-- statement:
--   A **birth–death process** has states $n \in \{0, 1, 2, \dots\}$. In state $n$ births (arrivals) occur at rate $\lambda_n$ and, for $n \ge 1$, deaths (departures) occur at rate $\mu_n$. This module fixes the vocabulary of Chapter 2.
--
--   1. For rate sequences $(\lambda_n)$ and $(\mu_n)$, the product
--   $$\prod_{i=1}^{n} \frac{\lambda_{i-1}}{\mu_i}, \qquad n \ge 0,$$
--   with the empty product equal to $1$ at $n = 0$.
--   2. The **global balance equations** (2.1):
--   $$(\lambda_n + \mu_n)\,p_n = \lambda_{n-1}p_{n-1} + \mu_{n+1}p_{n+1} \quad (n \ge 1), \qquad \lambda_0 p_0 = \mu_1 p_1.$$
--   3. A **steady-state solution** is a sequence $\{p_n\}$ with $p_n \ge 0$, $\sum_{n\ge 0} p_n = 1$, that solves (2.1). This is the book's convention (§1.9 and §2.1): the steady-state probabilities are the probability solution of $\mathbf 0 = \mathbf p Q$.
--   4. The rates of the models of the chapter: the $M/M/c$ death rates (2.30), $\mu_n = n\mu$ for $1 \le n < c$ and $\mu_n = c\mu$ for $n \ge c$, i.e. $\mu_n = \min(n, c)\,\mu$; the truncated arrival rates of §2.5, $\lambda_n = \lambda$ for $n < K$ and $\lambda_n = 0$ for $n \ge K$; and the $M/M/\infty$ death rates $\mu_n = n\mu$ (§2.7).
--
--   The $M/M/1$ queue is the case $\lambda_n = \lambda$, $\mu_n = \mu$; the $M/M/c$ queue has $\lambda_n = \lambda$ and the rates (2.30); the Erlang loss system $M/M/c/c$ has the truncated arrival rates with $K = c$ and the rates (2.30).
--
--   **Formalization Note** Rates are functions $\mathbb N \to \mathbb R$; the value of $\mu_0$ never enters the equations. The distribution is a real sequence with `HasSum p 1`, which also asserts that the series converges.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.49–51, §2.1, Eqs. (2.1), (2.3); p.67, Eq. (2.30); p.76, §2.5; p.84, §2.7

import Mathlib

namespace QueueingFundamentals.BirthDeath

/-- The product `∏_{i=1}^{n} λ_{i-1}/μ_i` of (2.3), p.51; it equals `1` for `n = 0`
(the empty product, as the book states on p.51). -/
noncomputable def bdProd (lam mu : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, lam (i - 1) / mu i

/-- The global balance equations (2.1), p.50, of the birth–death process with birth rates
`λ_n` (`n ≥ 0`) and death rates `μ_n` (`n ≥ 1`):
`(λ_n + μ_n) p_n = λ_{n-1} p_{n-1} + μ_{n+1} p_{n+1}` for `n ≥ 1`, and `λ_0 p_0 = μ_1 p_1`.
The value `mu 0` never enters. -/
def IsBalanced (lam mu : ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      (lam n + mu n) * p n = lam (n - 1) * p (n - 1) + mu (n + 1) * p (n + 1)) ∧
    lam 0 * p 0 = mu 1 * p 1

/-- A steady-state solution of the birth–death process (§1.9 and §2.1, pp.34, 50): a probability
distribution `{p_n}` on `{0, 1, 2, …}` (nonnegative, summing to one) that solves the balance
equations (2.1). -/
def IsSteadyState (lam mu : ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ IsBalanced lam mu p

/-- The death rates (2.30), p.67, of the `M/M/c` queue: `μ_n = nμ` for `1 ≤ n < c` and `μ_n = cμ`
for `n ≥ c`, i.e. `μ_n = min(n, c) μ`. (Its value at `n = 0` is never used.) -/
noncomputable def mmcDeath (mu : ℝ) (c : ℕ) (n : ℕ) : ℝ :=
  ((min n c : ℕ) : ℝ) * mu

/-- The birth rates of a queue with truncation at `K` (§2.5, p.76): `λ_n = λ` for `n < K` and
`λ_n = 0` whenever `n ≥ K`. -/
noncomputable def truncArrival (lam : ℝ) (K : ℕ) (n : ℕ) : ℝ :=
  if n < K then lam else 0

/-- The death rates of the `M/M/∞` queue (§2.7, p.84): `μ_n = nμ` for all `n`. -/
noncomputable def infDeath (mu : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * mu

end QueueingFundamentals.BirthDeath


