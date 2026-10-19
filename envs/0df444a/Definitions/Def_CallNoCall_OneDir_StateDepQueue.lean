-- Prove2me | Definitions.Def_CallNoCall_OneDir_StateDepQueue
-- name    : CallNoCall_OneDir_StateDepQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:33.173826+00:00
-- url     : https://prove2.me/theorems/126a0118-a716-4540-a9b0-eeb58a9aea04
-- title:
--   Appendix A, p. 34 — the average waiting time W of a state-dependent M/M/k queue, in closed form
-- statement:
--   Consider a **state-dependent $M/M/k$ queue**: customers arrive as a Poisson process of rate $\lambda \ge 0$, and when there are $n \ge 1$ customers in the system they leave at rate $\mu_n > 0$. The queue is described by the rate sequence $(\mu_n)_{n \ge 1}$ and the arrival rate $\lambda$.
--
--   1. For $i \ge 0$ write $\mu_1\mu_2\cdots\mu_i$ for the product of the first $i$ rates, with the empty product equal to $1$ at $i = 0$.
--   2. The waiting time is **finite** ($\mathcal W < \infty$) when both series
--   $$\sum_{i=1}^{\infty} \frac{i\lambda^{i-1}}{\mu_1\mu_2\cdots\mu_i}, \qquad \sum_{i=1}^{\infty} \frac{\lambda^{i}}{\mu_1\mu_2\cdots\mu_i}$$
--   converge.
--   3. Given a mean ride distance $d$ and a speed $v$, the **average waiting time** (from arrival to pick-up) is
--   $$\mathcal W = \frac{\sum_{i=1}^{\infty} \frac{i\lambda^{i-1}}{\mu_1\mu_2\cdots\mu_i}}{1 + \sum_{i=1}^{\infty} \frac{\lambda^{i}}{\mu_1\mu_2\cdots\mu_i}} - \frac{d}{v}.$$
--
--   This is the formula of Feng, Kong and Wang (Appendix A, p. 34), obtained "by standard queueing theory": the stationary distribution of the birth–death chain is proportional to $\lambda^i/(\mu_1\cdots\mu_i)$, the quotient of the two series is the mean number in system divided by $\lambda$ (the mean sojourn time, by Little's law), and subtracting the mean ride time $d/v$ leaves the time from arrival to pick-up. The paper uses it for both of its approximated ride-hailing systems; it is defined here for an arbitrary rate sequence so that the comparison principles of the mission are stated for every state-dependent $M/M/k$ queue.
--
--   **Formalization Note** The rates are a function $\mathbb N \to \mathbb R$ whose value at $0$ never enters. Both series are indexed from $i = 1$; the "$1 +$" in the denominator is the $i = 0$ term. "$\mathcal W < \infty$" is the predicate `FiniteWait` (both series `Summable`), as in the paper's proof of Theorem 1(1) ("It is equivalent to show … are both finite"). The real number `avgWait` is the paper's $\mathcal W$ only under `FiniteWait`: Lean's `tsum` of a divergent series is $0$, so every theorem that compares waiting times also asserts or assumes `FiniteWait`. Lean's convention $0^0 = 1$ makes the first numerator term $1/\mu_1$ also at $\lambda = 0$, so $\mathcal W = 1/\mu_1 - d/v$ there, the paper's value (proof of Theorem 5, p. 39).
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), p. 34, Appendix A, proof of Theorem 1, Part 1 (the waiting-time formula)

import Mathlib

namespace CallNoCall.OneDir

/-- The product `μ₁ μ₂ ⋯ μᵢ` of the first `i` service rates of a state-dependent `M/M/k` queue
(Appendix A, p. 34). The empty product at `i = 0` is `1`; the value `μ 0` never enters. -/
noncomputable def prodRates (μ : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 i, μ j

/-- The `i`-th term `i λ^{i-1} / (μ₁ ⋯ μᵢ)` of the numerator series of the waiting-time formula
(Appendix A, p. 34). It is used for `i ≥ 1` only. -/
noncomputable def numTerm (μ : ℕ → ℝ) (lam : ℝ) (i : ℕ) : ℝ :=
  (i : ℝ) * lam ^ (i - 1) / prodRates μ i

/-- The `i`-th term `λ^i / (μ₁ ⋯ μᵢ)` of the denominator series of the waiting-time formula
(Appendix A, p. 34). It is used for `i ≥ 1` only. -/
noncomputable def denTerm (μ : ℕ → ℝ) (lam : ℝ) (i : ℕ) : ℝ :=
  lam ^ i / prodRates μ i

/-- The paper's "`W < ∞`" (Appendix A, p. 34): both series `∑_{i ≥ 1} i λ^{i-1}/(μ₁⋯μᵢ)` and
`∑_{i ≥ 1} λ^i/(μ₁⋯μᵢ)` converge. -/
def FiniteWait (μ : ℕ → ℝ) (lam : ℝ) : Prop :=
  Summable (fun i : ℕ => numTerm μ lam (i + 1)) ∧ Summable (fun i : ℕ => denTerm μ lam (i + 1))

/-- The average waiting time (arrival to pick-up) of a state-dependent `M/M/k` queue with arrival
rate `λ` and service rate `μₙ` in state `n ≥ 1`, in the closed form of Appendix A, p. 34:
`W = (∑_{i ≥ 1} i λ^{i-1}/(μ₁⋯μᵢ)) / (1 + ∑_{i ≥ 1} λ^i/(μ₁⋯μᵢ)) - d/v`.
Both series are indexed from `i = 1`; the `1 +` is the `i = 0` term. The value is meaningful only
under `FiniteWait μ lam`. -/
noncomputable def avgWait (μ : ℕ → ℝ) (lam d v : ℝ) : ℝ :=
  (∑' i : ℕ, numTerm μ lam (i + 1)) / (1 + ∑' i : ℕ, denTerm μ lam (i + 1)) - d / v

end CallNoCall.OneDir


