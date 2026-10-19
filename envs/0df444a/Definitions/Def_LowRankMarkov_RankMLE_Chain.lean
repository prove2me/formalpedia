-- Prove2me | Definitions.Def_LowRankMarkov_RankMLE_Chain
-- name    : LowRankMarkov_RankMLE_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:49.050323+00:00
-- url     : https://prove2.me/theorems/89acd45e-1299-4931-82c8-3e5d359d51ad
-- title:
--   §3, §3.1, Definition 1, pp. 6–7 — finite Markov chain: stochastic matrix, stationary law, primitivity, π_min, π_max, trajectory law, ⟨·,·⟩_π, P*, ρ₊
-- statement:
--   This file fixes the finite Markov chain of §3 of Zhu, Li, Wang and Zhang and its right spectral gap. The state space is $[p]=\{s_1,\dots,s_p\}$.
--
--   1. A **transition matrix** is a matrix $P\in\mathbb R^{p\times p}$ with $P_{ij}\ge 0$ and $\sum_{j}P_{ij}=1$ for every $i$; $P_{ij}=\mathbb P(X_1=s_j\mid X_0=s_i)$.
--   2. A **stationary distribution** of $P$ is a probability vector $\pi$ ($\pi_i\ge0$, $\sum_i\pi_i=1$) with $\sum_i \pi_iP_{ij}=\pi_j$ for every $j$.
--   3. $P$ is **primitive** if some power $P^t$ has all entries positive; for a finite chain this is "irreducible and aperiodic", which is how the paper's "ergodic Markov chain" is read.
--   4. $\pi_{\min}:=\min_j\pi_j$ and $\pi_{\max}:=\max_j\pi_j$.
--   5. **Trajectory law.** A trajectory $x=(X_0,\dots,X_n)$ makes $n$ transitions. Under the chain started from the initial law $\pi$ its probability is
--   $$\pi(x_0)\prod_{k=0}^{n-1}P_{x_k x_{k+1}},$$
--   and the probability $\mathbb P(E)$ of an event $E$ is the sum of these weights over the trajectories in $E$.
--   6. **Right spectral gap** (Definition 1). With the inner product $\langle h_1,h_2\rangle_\pi=\sum_j h_{1j}h_{2j}\pi_j$ and the adjoint $P^*=\mathrm{Diag}(\pi)^{-1}P^\top\mathrm{Diag}(\pi)$, i.e. $P^*_{ij}=\pi_jP_{ji}/\pi_i$,
--   $$\rho_+:=\sup_{\langle h,1\rangle_\pi=0,\ \langle h,h\rangle_\pi=1}\ \tfrac12\langle (P+P^*)h,h\rangle_\pi ,$$
--   and the right $\mathcal L_2$-spectral gap of $P$ is $1-\rho_+$.
--
--   These are the objects in which the paper's statistical guarantees for low-rank Markov chain estimation are stated: the rate of Theorem 2 depends on $\pi_{\min}$, $\pi_{\max}$ and the condition $n\pi_{\max}(1-\rho_+)>\max(20\log p,\log n)$.
--
--   **Formalization Note** States are `Fin p` (index base $0$). The definitions are total; that $P$ is stochastic, that $\pi$ is stationary and positive, and $p\ge2$ are hypotheses of the theorems. When $\pi$ is the initial law, `trajProb` is the law of the chain started at stationarity ($X_0\sim\pi$). $\rho_+$ is a real supremum (`sSup`); for $p\ge2$ and $\pi>0$ the set is nonempty and bounded, so this is the true supremum. Definition 1's requirement $\rho_+<1$ is not part of the definition: the theorems that need it state it, or imply it. $P^*$ is written entrywise and kept literally, although $\langle P^*h,h\rangle_\pi=\langle Ph,h\rangle_\pi$.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 6 (§3, first paragraph), p. 7 (§3.1, ⟨·,·⟩_π, P*, Definition 1)

import Mathlib

namespace LowRankMarkov.RankMLE

open Matrix

/-- `P` is a transition probability matrix on the `p` states `Fin p`: nonnegative entries and unit
row sums, `P i j = ℙ(X₁ = s_j | X₀ = s_i)` (§3, p. 6). -/
def IsStochastic {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- `π` is a stationary distribution of `P`: a probability vector with `πᵀP = πᵀ` (§3, p. 6). -/
def IsStationary {p : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ ∀ j, ∑ i, π i * P i j = π j

/-- Ergodicity of a finite chain, encoded as primitivity: some power of `P` has all entries
positive (irreducible and aperiodic) (§3, p. 6, "an ergodic Markov chain"). -/
def IsPrimitive {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∃ t : ℕ, ∀ i j, 0 < (P ^ t) i j

/-- `π_min := min_{j ∈ [p]} π_j` (§3, p. 6). -/
noncomputable def piMin {p : ℕ} (π : Fin p → ℝ) : ℝ :=
  ⨅ i, π i

/-- `π_max := max_{j ∈ [p]} π_j` (§3, p. 6). -/
noncomputable def piMax {p : ℕ} (π : Fin p → ℝ) : ℝ :=
  ⨆ i, π i

/-- The probability weight of the trajectory `x = (X₀, …, X_n)` (`n` transitions) of the chain
started from `π`: `π(x₀) ∏_{k<n} P(x_k, x_{k+1})`. -/
def trajWeight {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (x : Fin (n + 1) → Fin p) : ℝ :=
  π (x 0) * ∏ k : Fin n, P (x k.castSucc) (x k.succ)

open Classical in
/-- The probability `ℙ(E)` of an event `E` of the trajectory `(X₀, …, X_n)` under the law of the
chain with initial law `π` and transition matrix `P` (a finite sum over the `p^{n+1}`
trajectories). -/
noncomputable def trajProb {p n : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (E : (Fin (n + 1) → Fin p) → Prop) : ℝ :=
  ∑ x, if E x then trajWeight π P x else 0

/-- The inner product of `L₂(π)`: `⟨h₁, h₂⟩_π := ∑_j h_{1j} h_{2j} π_j` (§3.1, p. 7). -/
def piInner {p : ℕ} (π : Fin p → ℝ) (h₁ h₂ : Fin p → ℝ) : ℝ :=
  ∑ j, h₁ j * h₂ j * π j

/-- The `L₂(π)`-adjoint `P* = Diag(π)⁻¹ Pᵀ Diag(π)`, entrywise `P*_{ij} = π_j P_{ji} / π_i`
(§3.1, p. 7). -/
noncomputable def Pstar {p : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j => π j * P j i / π i

/-- Definition 1 (p. 7): `ρ₊ := sup_{⟨h,1⟩_π = 0, ⟨h,h⟩_π = 1} ½⟨(P + P*)h, h⟩_π`; the right
`L₂`-spectral gap of `P` is `1 − ρ₊`. The condition `ρ₊ < 1` is not built in. -/
noncomputable def rhoPlus {p : ℕ} (π : Fin p → ℝ) (P : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  sSup {ρ : ℝ | ∃ h : Fin p → ℝ, piInner π h (fun _ => 1) = 0 ∧ piInner π h h = 1 ∧
    ρ = (1 / 2) * piInner π ((P + Pstar π P) *ᵥ h) h}

end LowRankMarkov.RankMLE


