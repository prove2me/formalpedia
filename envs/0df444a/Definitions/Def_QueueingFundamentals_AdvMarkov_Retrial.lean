-- Prove2me | Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial
-- name    : QueueingFundamentals_AdvMarkov_Retrial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:22:44.241875+00:00
-- url     : https://prove2.me/theorems/83f9baf4-d718-4ffc-869e-c5a82e042e3d
-- title:
--   The M/M/1 retrial queue: rate-balance equations (3.47)–(3.49), steady-state solutions, generating functions and the closed form (3.57)
-- statement:
--   The **$M/M/1$ retrial queue** of §3.5.1 has Poisson arrivals at rate $\lambda$, exponential service at rate $\mu$ and a single server. An arrival that finds the server busy enters the **orbit** and retries after an exponential time with mean $1/\gamma$, independently of everything else; no customer leaves because of impatience. With $i \in \{0,1\}$ the number in service and $n \in \{0,1,2,\dots\}$ the number in orbit, $p_{i,n}$ is the steady-state probability of state $\{i,n\}$. This module fixes four objects.
--
--   1. The **rate-balance equations** (3.47)–(3.49):
--   $$\begin{aligned}
--   (\lambda + n\gamma)\,p_{0,n} &= \mu\,p_{1,n}, && n \ge 0,\\
--   (\lambda+\mu)\,p_{1,n} &= \lambda p_{0,n} + (n+1)\gamma\,p_{0,n+1} + \lambda p_{1,n-1}, && n \ge 1,\\
--   (\lambda+\mu)\,p_{1,0} &= \lambda p_{0,0} + \gamma\,p_{0,1}.
--   \end{aligned}$$
--   2. A **steady-state solution**: sequences $p_{0,n}, p_{1,n} \ge 0$ with $\sum_{n \ge 0}(p_{0,n} + p_{1,n}) = 1$ that solve these equations. This is the book's convention (§1.9, and the footnote on p.118): the steady-state probabilities are the probability solution of the balance equations.
--   3. The **generating function** $\sum_{n\ge 0} z^n p_n$ of a sequence at a real argument $z$; in particular the partial generating functions
--   $$P_0(z) = \sum_{n=0}^\infty z^n p_{0,n}, \qquad P_1(z) = \sum_{n=0}^\infty z^n p_{1,n}.$$
--   4. The closed form (3.57): with $\rho = \lambda/\mu$,
--   $$p_{0,n} = (1-\rho)^{(\lambda/\gamma)+1}\,\frac{\rho^n}{n!\,\gamma^n}\prod_{i=0}^{n-1}(\lambda + i\gamma), \qquad p_{1,n} = (1-\rho)^{(\lambda/\gamma)+1}\,\frac{\rho^{n+1}}{n!\,\gamma^n}\prod_{i=1}^{n}(\lambda + i\gamma),$$
--   where an empty product equals $1$.
--
--   **Formalization Note** The exponent $(\lambda/\gamma)+1$ is a real power; the closed form is meaningful for $\rho < 1$, and every theorem that uses it assumes $0 < \lambda < \mu$ and $\gamma > 0$. The total mass is stated with `HasSum`, which also asserts convergence. The generating function is a `tsum`; it is used only for $|z| \le 1$, where the series converge absolutely for a probability solution.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.159, §3.5.1, Eqs. (3.47)–(3.49) and the partial generating functions; p.161, Eq. (3.57)

import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- The rate-balance equations (3.47)–(3.49), p.159, of the `M/M/1` retrial queue (§3.5.1) with
arrival rate `λ`, service rate `μ` and retrial rate `γ` per customer in orbit. The state `{i, n}`
has `i ∈ {0, 1}` customers in service and `n` in orbit; `p0 n = p_{0,n}` and `p1 n = p_{1,n}`.
* (3.47) `(λ + nγ) p_{0,n} = μ p_{1,n}` for `n ≥ 0`;
* (3.48) `(λ + μ) p_{1,n} = λ p_{0,n} + (n + 1)γ p_{0,n+1} + λ p_{1,n−1}` for `n ≥ 1`;
* (3.49) `(λ + μ) p_{1,0} = λ p_{0,0} + γ p_{0,1}`. -/
def RetrialBalance (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, (lam + (n : ℝ) * gam) * p0 n = mu * p1 n) ∧
    (∀ n : ℕ, 1 ≤ n →
      (lam + mu) * p1 n = lam * p0 n + ((n : ℝ) + 1) * gam * p0 (n + 1) + lam * p1 (n - 1)) ∧
    (lam + mu) * p1 0 = lam * p0 0 + gam * p0 1

/-- A steady-state solution of the `M/M/1` retrial queue (book convention, §1.9 p.34 and the
footnote on p.118): a probability distribution `{p_{i,n}}` on `{0, 1} × {0, 1, 2, …}` —
nonnegative, with total mass `∑_n (p_{0,n} + p_{1,n}) = 1` — that solves (3.47)–(3.49). -/
def IsRetrialSteadyState (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p0 n) ∧ (∀ n : ℕ, 0 ≤ p1 n) ∧ HasSum (fun n : ℕ => p0 n + p1 n) 1 ∧
    RetrialBalance lam mu gam p0 p1

/-- The (partial) generating function `∑_{n ≥ 0} zⁿ p_n` of a sequence, for a real argument `z`
(p.159: `P_0(z) ≡ ∑ zⁿ p_{0,n}`, `P_1(z) ≡ ∑ zⁿ p_{1,n}`). -/
noncomputable def pgf (p : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ n * p n

/-- The closed form of `p_{0,n}` in (3.57), p.161, with `ρ = λ/μ`:
`p_{0,n} = (1 − ρ)^{(λ/γ)+1} · ρⁿ/(n! γⁿ) · ∏_{i=0}^{n−1} (λ + iγ)` (empty product `= 1`).
The exponent `(λ/γ) + 1` is a real power (`Real.rpow`). -/
noncomputable def retrialP0 (lam mu gam : ℝ) (n : ℕ) : ℝ :=
  (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ n / ((n.factorial : ℝ) * gam ^ n)) *
    ∏ i ∈ Finset.range n, (lam + (i : ℝ) * gam)

/-- The closed form of `p_{1,n}` in (3.57), p.161, with `ρ = λ/μ`:
`p_{1,n} = (1 − ρ)^{(λ/γ)+1} · ρ^{n+1}/(n! γⁿ) · ∏_{i=1}^{n} (λ + iγ)` (empty product `= 1`). -/
noncomputable def retrialP1 (lam mu gam : ℝ) (n : ℕ) : ℝ :=
  (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ (n + 1) / ((n.factorial : ℝ) * gam ^ n)) *
    ∏ i ∈ Finset.Icc 1 n, (lam + (i : ℝ) * gam)

end QueueingFundamentals.AdvMarkov


