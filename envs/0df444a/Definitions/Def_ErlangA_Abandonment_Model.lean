-- Prove2me | Definitions.Def_ErlangA_Abandonment_Model
-- name    : ErlangA_Abandonment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:46.609638+00:00
-- url     : https://prove2.me/theorems/7c8602a8-314f-4a26-a83d-d2c0b63b9805
-- title:
--   The Erlang-A queue $M/M/N+M$: death rates, stationary law $\pi$ and abandonment probability $P_N\{Ab\}$
-- statement:
--   The **Erlang-A queue** ($M/M/N+M$) has Poisson arrivals at rate $\lambda>0$, $N\ge1$ statistically identical agents with exponential service times of rate $\mu>0$, an unlimited waiting room served in order of arrival, and customers whose patience is exponential with rate $\theta>0$, independent of everything else; a waiting customer whose wait reaches his patience abandons and does not return. This module defines three objects.
--
--   1. **Death rates.** The number in system $Q$ is a birth–death process with birth rate $\lambda$ in every state and, in state $k$, death rate
--   $$
--   \mu_k=\min(k,N)\,\mu+(k-N)^+\,\theta .
--   $$
--   2. **Stationary law** (Appendix B, p. 222, with buffer $B=\infty$). With the unnormalized weights
--   $$
--   w_k=\begin{cases}\dfrac{(\lambda/\mu)^k}{k!}, & 0\le k\le N,\\[2mm] \displaystyle\prod_{j=N+1}^{k}\frac{\lambda}{N\mu+(j-N)\theta}\cdot\frac{(\lambda/\mu)^N}{N!}, & k>N,\end{cases}
--   $$
--   the stationary probabilities are $\pi_k=w_k/\sum_{j\ge0}w_j$, so that $\pi_0^{-1}=\sum_{j\ge0}w_j$ is the paper's bracket.
--   3. **Abandonment probability** $P_N\{Ab\}$, the probability that a customer arriving in steady state abandons (Table 3, p. 215: $P\{Ab\}=P\{V>X\}$ with $V$ the potential waiting time and $X$ the patience). An arrival sees $k$ customers in system with probability $\pi_k$. If $k<N$ it is served at once. If $k=N+n$, its potential wait is a sum of independent exponentials of rates $N\mu+n\theta,\dots,N\mu+\theta,N\mu$ (Appendix B, p. 222), and it abandons with probability $(n+1)\theta/(N\mu+(n+1)\theta)$. Hence
--   $$
--   P_N\{Ab\}=\sum_{n\ge0}\pi_{N+n}\,\frac{(n+1)\theta}{N\mu+(n+1)\theta}.
--   $$
--
--   These are the objects of Theorem 1 of the paper; the blocking probability $P_N\{Bl\}$ of the loss system $M/M/N/N$ is Erlang's formula $E(\lambda/\mu,N)$, the published definition `KellyStochasticNetworks.erlang`.
--
--   **Formalization Note** The normalizing sum is a `tsum`, which Lean sets to $0$ when it diverges; the milestone `stationaryDist_isSteadyState` asserts that $\pi$ is a probability distribution (summable, total mass one) solving the balance equations, which rules this out for every $N\ge1$, $\lambda,\mu,\theta>0$. The paper's equation (2) $\theta\,E[\#\text{waiting}]=\lambda P\{Ab\}$ gives the equivalent form $P_N\{Ab\}=(\theta/\lambda)\sum_k (k-N)^+\pi_k$; it is the milestone `abandonment_balance`. The subtraction $k-N$ on natural numbers is truncated, which is exactly $(k-N)^+$.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, pp. 209–210 (§1, the model), p. 215 (Table 3, P{Ab}), pp. 221–222 (Appendix B, stationary distribution π_k)

import Mathlib

namespace ErlangA.Abandonment

/-- Death rates of the Erlang-A (`M/M/N + M`) queue with `N` agents, service rate `μ` and
patience rate `θ` (Garnett–Mandelbaum–Reiman 2002, §1, pp. 209–210; App. B, p. 222): in state
`k` (customers in system) the `min(k, N)` busy agents complete services at rate `μ` each and each
of the `(k − N)⁺` waiting customers abandons at rate `θ`. The birth rate is `λ` in every state.
(`k - N` is truncated subtraction on `ℕ`, which is exactly `(k − N)⁺`.) -/
noncomputable def deathRate (N : ℕ) (μ θ : ℝ) (k : ℕ) : ℝ :=
  ((min k N : ℕ) : ℝ) * μ + ((k - N : ℕ) : ℝ) * θ

/-- Unnormalized stationary weight `π_k / π_0` of App. B, p. 222, with `B = ∞`:
`(λ/μ)^k / k!` for `0 ≤ k ≤ N`, and
`∏_{j=N+1}^{k} λ/(Nμ + (j − N)θ) · (λ/μ)^N / N!` for `k > N`. -/
noncomputable def weight (N : ℕ) (lam μ θ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ N then (lam / μ) ^ k / (Nat.factorial k : ℝ)
  else (∏ j ∈ Finset.Icc (N + 1) k, lam / ((N : ℝ) * μ + ((j - N : ℕ) : ℝ) * θ)) *
    ((lam / μ) ^ N / (Nat.factorial N : ℝ))

/-- The stationary distribution `π_k = weight k / Σ_j weight j` of the number in system of the
Erlang-A queue (App. B, p. 222, `B = ∞`; the bracket is `π_0⁻¹`). The sum is a `tsum`; that it
converges and that this `π` is the unique steady state is the milestone
`ErlangA.Abandonment.stationaryDist_isSteadyState`. -/
noncomputable def stationaryDist (N : ℕ) (lam μ θ : ℝ) (k : ℕ) : ℝ :=
  weight N lam μ θ k / ∑' j, weight N lam μ θ j

/-- `P_N{Ab}`: the probability that a customer arriving in steady state abandons, `P{X < V}`
(Table 3, p. 215). An arrival finds `k` in system with probability `π_k` (PASTA). If `k < N`
it is served at once (`V = 0`). If `k = N + n` (`n` waiting), its potential wait `V` is a sum of
independent exponentials of rates `Nμ + nθ, …, Nμ + θ, Nμ` (App. B, p. 222), so it abandons
before entering service with probability `(n + 1)θ / (Nμ + (n + 1)θ)`. Hence
`P_N{Ab} = Σ_{n ≥ 0} π_{N+n} · (n + 1)θ / (Nμ + (n + 1)θ)`. -/
noncomputable def probAbandon (N : ℕ) (lam μ θ : ℝ) : ℝ :=
  ∑' n : ℕ, stationaryDist N lam μ θ (N + n) *
    (((n : ℝ) + 1) * θ / ((N : ℝ) * μ + ((n : ℝ) + 1) * θ))

end ErlangA.Abandonment


