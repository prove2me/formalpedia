-- Prove2me | Definitions.Def_StableDispatch_Markov_Setting
-- name    : StableDispatch_Markov_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:14.215651+00:00
-- url     : https://prove2.me/theorems/22ff3096-1a1e-4103-8a7c-bd1d905e7fb6
-- title:
--   §2.1–§2.2, §2.4, Appendix A — Σ_n (2.1), the single-ID policy's CTMC (Q, I) and its generator, the stability region, and the Lyapunov objects (A.1)–(A.2)
-- statement:
--   This file fixes the model of §2.1–§2.2 of Gamarnik, Tsitsiklis and Zubeldia and the objects used in the proof of their Theorem 2.1 (Appendix A).
--
--   **Servers and rates.** There are $n$ parallel servers, each with an infinite-capacity FIFO queue. Server $j$ has service rate $\mu_j>0$, and the total processing power is $n$, so the rate vector lies in
--   $$\Sigma_n=\Big\{\mu\in(0,\infty)^n:\ \sum_{i=1}^n\mu_i=n\Big\}\qquad(2.1).$$
--   Jobs arrive as a Poisson process of rate $\lambda n$ and have i.i.d. exponential sizes of unit mean, so a busy server $j$ completes jobs at rate $\mu_j$.
--
--   **The policy.** The dispatcher stores the ID $i$ of one server. Each server sends its queue length to the dispatcher as a Poisson process of rate $\alpha_n>0$; on a message from server $j$, the dispatcher replaces the stored ID by $j$ exactly when $q_j<q_i$. Every arriving job is sent to the stored server, and arrivals and departures never change the stored ID.
--
--   **The Markov chain.** A state is a pair $(q,i)$ with $q\in\mathbb Z_+^n$ the vector of queue lengths (jobs in queue or in service) and $i$ the stored ID. Writing $e_j$ for the $j$-th unit vector, the transition rates of Appendix A are
--   $$r_{(q,i)\to(q+e_i,i)}=\lambda n,\qquad r_{(q,i)\to(q-e_j,i)}=\mu_j\,\mathbb 1_{[1,\infty)}(q_j),\qquad r_{(q,i)\to(q,j)}=\alpha_n\,\mathbb 1_{[0,q_i-1]}(q_j),$$
--   and all other off-diagonal rates are $0$. The generator $Q$ has these off-diagonal entries and diagonal entry $Q_{(q,i),(q,i)}=-\big(\lambda n+\sum_j\mu_j\mathbb 1\{q_j\ge1\}+\alpha_n\,\#\{j:q_j<q_i\}\big)$, minus the total rate of leaving $(q,i)$.
--
--   **Stability region.** For fixed $n$, $\lambda$ and $\alpha_n$, the stability region is the set of $\mu\in\Sigma_n$ for which the chain $(Q(\cdot),I(\cdot))$ is positive recurrent (every state has a finite expected return time), in the sense of the published definition `MatrixAnalytic.Tree.IsPositiveRecurrentProcess`.
--
--   **Lyapunov objects (Appendix A).** For $n\ge1$, let $\mu_{\max}=\max_j\mu_j$ and $\mu_{\min}=\min_j\mu_j$, and
--   $$\Xi_1(q,i)=\frac{2\mu_{\max}}{\alpha_n}q_i,\qquad \Xi_2(q,i)=\sum_{j=1}^n q_j^2,\qquad \Xi=\Xi_1+\Xi_2\quad(A.1),$$
--   $$F_n=\Big\{(q,i):\ \sum_{j=1}^n q_j<\frac{\lambda n\big(1+\frac{2\mu_{\max}}{\alpha_n}\big)+n+1}{2\min\{1-\lambda,\mu_{\min}\}}\Big\}\quad(A.2).$$
--
--   These are the objects in which Theorem 2.1 and the drift computations of its proof are stated.
--
--   **Formalization Note.** Servers $\{1,\dots,n\}$ are `Fin n` (0-based); a state is `(Fin n → ℕ) × Fin n`. The parameter `lam` is $\lambda$ and `α` is $\alpha_n$, a single positive real for the fixed $n$. The diagonal of the generator is written as the finite sum above. `muMax`, `muMin`, `Xi1`, `Xi`, `Fn` require `[NeZero n]` because the maximum and minimum of an empty family are undefined; `Fn` is defined as a set, and its finiteness is a theorem (milestone), not part of the definition.
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, pp. 5–6, 11–12, 14–15, (2.1), §2.2.1, §2.2.2, §2.4, Appendix A items 1–4, (A.1), (A.2)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process

namespace StableDispatch.Markov

noncomputable section

/-- A state `(q, i)` of the chain `(Q(·), I(·))` of §2.2.2: the queue lengths `q j` (jobs in
queue or in service at server `j`) and the ID `i` of the server stored in the dispatcher's
memory. Servers `{1, …, n}` are indexed by `Fin n` (0-based). The state space is
`Zⁿ₊ × {1, …, n}` (Appendix A, p. 14). -/
abbrev State (n : ℕ) := (Fin n → ℕ) × Fin n

/-- The set `Σ_n` of admissible service-rate vectors, (2.1), p. 5:
`Σ_n = {μ ∈ (0, ∞)^n : Σ_i μ_i = n}`. -/
def Sigma (n : ℕ) : Set (Fin n → ℝ) :=
  {μ | (∀ i, 0 < μ i) ∧ ∑ i, μ i = (n : ℝ)}

/-- The generator of the continuous-time Markov chain `(Q(·), I(·))` of the single-ID policy
(§2.2.1; transition rates of Appendix A, items 1–4, pp. 14–15), with arrival-rate parameter
`lam` (λ; total arrival rate `λn`), per-server message rate `α` (`α_n`) and service rates `μ`.
From the state `x = (q, i)`, the off-diagonal rate toward `y ≠ x` is the sum of
1. `λn` if `y = (q + e_i, i)`: every arriving job is sent to the server whose ID is stored, and
   the stored ID does not change on an arrival (item 1);
2. `μ_j` if `q_j ≥ 1` and `y = (q − e_j, i)`, for each server `j`: a service completion at `j`
   (unit-mean exponential job sizes, so server `j` completes at rate `μ_j`); the stored ID does
   not change (item 2);
3. `α_n` if `q_j < q_i` and `y = (q, j)`, for each server `j`: a message from `j` (Poisson of rate
   `α_n`) makes the dispatcher store `j` exactly when `j`'s queue is shorter than the stored
   server's (item 3, rate `α_n 1_{[0, q_i − 1]}(q_j)`);

and every other off-diagonal rate is `0` (item 4). These three kinds of targets are pairwise
distinct and never equal `x`. The diagonal entry is minus the total exit rate,
`−(λn + Σ_j μ_j 1{q_j ≥ 1} + α_n · #{j : q_j < q_i})`. -/
def gen (n : ℕ) (lam α : ℝ) (μ : Fin n → ℝ) (x y : State n) : ℝ :=
  if y = x then
    -(lam * n + ∑ j, (if 1 ≤ x.1 j then μ j else 0)
        + ∑ j, (if x.1 j < x.1 x.2 then α else 0))
  else
    (if y = (Function.update x.1 x.2 (x.1 x.2 + 1), x.2) then lam * n else 0)
      + ∑ j, (if 1 ≤ x.1 j ∧ y = (Function.update x.1 j (x.1 j - 1), x.2) then μ j else 0)
      + ∑ j, (if x.1 j < x.1 x.2 ∧ y = (x.1, j) then α else 0)

/-- The stability region of the single-ID policy under arrival rate `λ` (§2.4, pp. 11–12, read
for the Markovian setting of §2.2.2): the rate vectors `μ ∈ Σ_n` for which the chain
`(Q(·), I(·))` is positive recurrent. -/
def stabilityRegion (n : ℕ) (lam α : ℝ) : Set (Fin n → ℝ) :=
  {μ | μ ∈ Sigma n ∧ MatrixAnalytic.Tree.IsPositiveRecurrentProcess (gen n lam α μ)}

/-- `μ_max = max_j μ_j` (Appendix A, (A.1)). -/
def muMax {n : ℕ} [NeZero n] (μ : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty μ

/-- `μ_min = min_j μ_j` (Appendix A, (A.2)). -/
def muMin {n : ℕ} [NeZero n] (μ : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty μ

/-- The Lyapunov function `Ξ1(q, i) = (2μ_max/α_n) q_i` (Appendix A, p. 15). -/
def Xi1 {n : ℕ} [NeZero n] (μ : Fin n → ℝ) (α : ℝ) (x : State n) : ℝ :=
  2 * muMax μ / α * (x.1 x.2 : ℝ)

/-- The Lyapunov function `Ξ2(q, i) = Σ_j q_j²` (Appendix A, p. 15). -/
def Xi2 {n : ℕ} (x : State n) : ℝ :=
  ∑ j, ((x.1 j : ℝ)) ^ 2

/-- The Lyapunov function `Ξ = Ξ1 + Ξ2`, (A.1), p. 15. -/
def Xi {n : ℕ} [NeZero n] (μ : Fin n → ℝ) (α : ℝ) (x : State n) : ℝ :=
  Xi1 μ α x + Xi2 x

/-- The set `F_n` of (A.2), p. 15: the states `(q, i)` with
`Σ_j q_j < (λn(1 + 2μ_max/α_n) + n + 1) / (2 min{1 − λ, μ_min})`. -/
def Fn (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) : Set (State n) :=
  {x | ∑ j, (x.1 j : ℝ) <
    (lam * n * (1 + 2 * muMax μ / α) + n + 1) / (2 * min (1 - lam) (muMin μ))}

end

end StableDispatch.Markov


