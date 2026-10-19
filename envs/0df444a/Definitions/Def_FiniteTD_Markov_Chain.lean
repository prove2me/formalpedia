-- Prove2me | Definitions.Def_FiniteTD_Markov_Chain
-- name    : FiniteTD_Markov_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:46.229987+00:00
-- url     : https://prove2.me/theorems/7452f662-4810-44b8-acf7-86afef7ee05d
-- title:
--   §2, §8, pp. 4–5, 16–17 — finite Markov chain: stochastic matrix, stationary π, trajectory law, d_TV, Assumption 1, τmix (21)
-- statement:
--   This file fixes the finite Markov chain on which temporal-difference learning is run, and the mixing notions of §8.
--
--   Let $S$ be a finite set of states. A function $P : S \times S \to \mathbb{R}$ is a **stochastic matrix** if $P(s,s') \ge 0$ and $\sum_{s'} P(s,s') = 1$ for every $s$; $P(s,s')$ is the probability $P(s'\mid s)$ of moving from $s$ to $s'$. A vector $\pi$ on $S$ is a **stationary distribution** of $P$ if $\pi(s)\ge 0$, $\sum_s \pi(s) = 1$ and
--   $$\sum_{s} \pi(s) P(s,s') = \pi(s') \quad \text{for all } s'.$$
--
--   **Trajectory law.** The chain started from $\pi$ visits $(s_0,\dots,s_k) = (w_0,\dots,w_k)$ with probability
--   $$\mathrm{pathProb}_k(w) = \pi(w_0)\prod_{i=0}^{k-1} P(w_i, w_{i+1}),$$
--   and the expectation of a function $F$ of the first $k+1$ states is the finite sum $\mathbb{E}[F(s_0,\dots,s_k)] = \sum_{w \in S^{k+1}} \mathrm{pathProb}_k(w)\,F(w)$. A finite trajectory $w_0,\dots,w_k$ is extended to all times by staying at $w_k$; the prefix $(s_0,\dots,s_t)$ and the window $(s_{t+\tau},\dots,s_{t+\tau+k})$ of a trajectory of length $t+\tau+k+1$ are also named here.
--
--   **Total variation and Assumption 1.** For vectors $p,q$ on $S$, $d_{TV}(p,q) = \tfrac12\sum_s |p(s)-q(s)|$. Assumption 1 with constants $m$ and $\rho$ says that $m>0$, $\rho\in(0,1)$ and
--   $$\sup_{s\in S} d_{TV}\big(P^t(s,\cdot),\,\pi\big) \le m\rho^t \quad \text{for all } t\in\mathbb{N}_0,$$
--   where $P^t$ is the $t$-th matrix power. The stationary start of Assumption 1 is built into the trajectory law above.
--
--   **Mixing time** (21). $\tau_{\mathrm{mix}}(\epsilon) = \min\{t\in\mathbb{N}_0 : m\rho^t \le \epsilon\}$.
--
--   **Formalization Note** The paper works with a finite state space (p. 5, Remark 1), so the law of $(s_0,\dots,s_k)$ is a finite sum and no measure theory is needed. $\tau_{\mathrm{mix}}$ is an infimum over $\mathbb{N}$; it takes the junk value $0$ when no $t$ qualifies, which happens only for $\epsilon \le 0$, and every statement of the mission evaluates it at a positive $\epsilon$.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, pp. 4–5 (§2), p. 16 (Assumption 1), p. 17 (21)

import Mathlib

namespace FiniteTD.Markov

/-- `P : S → S → ℝ` is a stochastic matrix: `P s s'` is the probability `P(s'|s)` of moving from `s` to `s'`. -/
def IsStochastic {S : Type} [Fintype S] (P : S → S → ℝ) : Prop :=
  (∀ s s', 0 ≤ P s s') ∧ ∀ s, ∑ s', P s s' = 1

/-- `π` is a stationary distribution of `P`: a probability vector with `πP = π`. -/
def IsStationaryDist {S : Type} [Fintype S] (P : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ s, 0 ≤ π s) ∧ ∑ s, π s = 1 ∧ ∀ s', ∑ s, π s * P s s' = π s'

/-- Probability that the chain with initial law `π` and kernel `P` visits `w 0, w 1, …, w k`. -/
noncomputable def pathProb {S : Type} [Fintype S] (π : S → ℝ) (P : S → S → ℝ) (k : ℕ)
    (w : Fin (k + 1) → S) : ℝ :=
  π (w 0) * ∏ i : Fin k, P (w i.castSucc) (w i.succ)

/-- Expectation `E[F(s₀, …, s_k)]` over the first `k + 1` states of the chain with initial law `π`
and kernel `P`, as a finite sum over trajectories. -/
noncomputable def pathExp {S : Type} [Fintype S] [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (k : ℕ)
    (F : (Fin (k + 1) → S) → ℝ) : ℝ :=
  ∑ w : Fin (k + 1) → S, pathProb π P k w * F w

/-- A finite trajectory `w 0, …, w k` extended to all times by staying at `w k` after time `k`. -/
def extendPath {S : Type} {k : ℕ} (w : Fin (k + 1) → S) : ℕ → S :=
  fun t => w ⟨min t k, by omega⟩

/-- The states `s₀, …, s_t` of a trajectory `s₀, …, s_{t+τ+k}`. -/
def pathPrefix {S : Type} (t τ k : ℕ) (w : Fin (t + τ + k + 1) → S) : Fin (t + 1) → S :=
  fun i => w ⟨i.1, by have := i.2; omega⟩

/-- The states `s_{t+τ}, …, s_{t+τ+k}` of a trajectory `s₀, …, s_{t+τ+k}`. -/
def pathWindow {S : Type} (t τ k : ℕ) (w : Fin (t + τ + k + 1) → S) : Fin (k + 1) → S :=
  fun j => w ⟨t + τ + j.1, by have := j.2; omega⟩

/-- Total-variation distance `d_TV(p, q) = ½ Σ_s |p(s) − q(s)|` between two vectors on `S`. -/
noncomputable def tvDist {S : Type} [Fintype S] (p q : S → ℝ) : ℝ :=
  (1 / 2) * ∑ s, |p s - q s|

/-- Assumption 1 (uniform geometric mixing): `m > 0`, `ρ ∈ (0, 1)` and
`sup_s d_TV(P^t(s, ·), π) ≤ m ρ^t` for every `t ∈ ℕ₀`. -/
def Assumption1 {S : Type} [Fintype S] [DecidableEq S] (P : S → S → ℝ) (π : S → ℝ) (m ρ : ℝ) : Prop :=
  0 < m ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ (t : ℕ) (s : S), tvDist (fun s' => (Matrix.of P ^ t) s s') π ≤ m * ρ ^ t

/-- The mixing time (21): `τmix(ε) = min {t ∈ ℕ₀ | m ρ^t ≤ ε}`. -/
noncomputable def tauMix (m ρ ε : ℝ) : ℕ :=
  sInf {t : ℕ | m * ρ ^ t ≤ ε}

end FiniteTD.Markov


