-- Prove2me | Definitions.Def_RelaxedIndexability_Arm
-- name    : RelaxedIndexability_Arm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:25.502342+00:00
-- url     : https://prove2.me/theorems/1546e856-7742-45ce-aff3-100304d0b856
-- title:
--   One arm of a partially observable restless bandit
-- statement:
--   An **arm** of a restless multi-armed bandit is a finite-state Markov chain together with a reward vector:
--
--   1. a number of states $K$, the states being $0, 1, \dots, K-1$;
--   2. a row-stochastic transition matrix $\mathbf P = (p_{ij})_{i,j=0}^{K-1}$: $p_{ij} \ge 0$ and $\sum_j p_{ij} = 1$ for every $i$;
--   3. a reward vector $B = (B_0, \dots, B_{K-1})$, where $B_i$ is the reward obtained when the arm is observed in state $i$.
--
--   The state of an arm is observed only when the arm is activated; otherwise the decision maker tracks a **belief** $\omega = (\omega_0, \dots, \omega_{K-1})$, a probability vector over the states. The $k$-th row of $\mathbf P$ is written $p_k = (p_{k0}, \dots, p_{k,K-1})$; it is the belief after the arm has been observed in state $k$.
--
--   A restless bandit with $N$ arms is a family of $N$ such arms, each with its own $K$, $\mathbf P$ and $B$, and a common discount factor $\beta \in (0,1)$.
--
--   **Formalization Note** States are `Fin K`, with the paper's own 0-based indexing. Row stochasticity is Mathlib's `Matrix.rowStochastic`. The paper's footnote on p.7 (each $\mathbf P$ irreducible and aperiodic, used only for the stationary initial belief (3)) and its normalization $0 = B_0 \le B_1 \le \dots \le B_{K-1}$ (p.11) are not part of the structure.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, §2, p.6 (model), p.7 (footnote on P), p.11 (rows p_k and reward convention)

import Mathlib

namespace RelaxedIndexability

/-- **One arm of a partially observable restless bandit** (Liu, *Relaxed Indexability and Index
Policy for Partially Observable Restless Bandits*, arXiv:2107.11939v4, §2, p.6): a finite-state
Markov chain with `K` states `0, …, K − 1`, row-stochastic transition matrix `P = (p_{ij})` and
reward vector `B = (B₀, …, B_{K−1})`, where `B_i` is the reward obtained when the arm is observed
in state `i`.

**Formalization Note.** States are `Fin K` with the paper's own 0-based indexing. Row
stochasticity is Mathlib's `Matrix.rowStochastic` (nonnegative entries, every row sums to `1`).
The footnote on p.7 (irreducible and aperiodic `P`, used only for the stationary initial belief (3))
and the normalization `0 = B₀ ≤ ⋯ ≤ B_{K−1}` of p.11 are not imposed. -/
structure Arm where
  /-- The number of states of the arm. -/
  K : ℕ
  /-- The transition matrix; row `i` is the law of the next state from state `i`. -/
  P : Matrix (Fin K) (Fin K) ℝ
  /-- The reward obtained when the arm is observed in state `i`. -/
  B : Fin K → ℝ
  /-- `P` is row stochastic. -/
  P_stochastic : P ∈ Matrix.rowStochastic ℝ (Fin K)

end RelaxedIndexability


