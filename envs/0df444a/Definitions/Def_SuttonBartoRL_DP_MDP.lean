-- Prove2me | Definitions.Def_SuttonBartoRL_DP_MDP
-- name    : SuttonBartoRL_DP_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:11:28.931996+00:00
-- url     : https://prove2.me/theorems/3aaed97f-3b60-4d5e-b9d6-386b119a3d64
-- title:
--   A finite MDP with four-argument dynamics $p(s', r \mid s, a)$, and policies
-- statement:
--   A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same in every state), a finite set of rewards $\mathcal R \subset \mathbb R$, and the **dynamics**
--   $$
--   p(s', r \mid s, a) \;=\; \Pr\{S_t = s',\, R_t = r \mid S_{t-1} = s,\, A_{t-1} = a\},
--   $$
--   which for each state–action pair $(s,a)$ is a probability distribution over next state and reward:
--   $$
--   p(s', r\mid s,a) \ge 0, \qquad \sum_{s' \in \mathcal S}\sum_{r \in \mathcal R} p(s', r \mid s, a) = 1 .
--   $$
--   From it one derives the state-transition probabilities $p(s' \mid s, a) = \sum_{r\in\mathcal R} p(s', r\mid s, a)$ (3.4) and the expected rewards $r(s,a) = \sum_{r\in\mathcal R} r \sum_{s'} p(s', r\mid s, a)$ (3.5).
--
--   A **policy** $\pi$ assigns to every state $s$ a probability distribution $\pi(a\mid s)$ over actions. A **deterministic policy** is a map $\pi : \mathcal S \to \mathcal A$; it is identified with the stochastic policy that selects $\pi(s)$ with probability one.
--
--   These are the objects on which every dynamic-programming result of Chapter 4 is stated.
--
--   **Formalization Note** The dynamics are a function `p s a s' r` on $\mathcal S \times \mathcal A \times \mathcal S \times \mathbb R$; its values at rewards outside the finite set $\mathcal R$ are never used, since every sum over rewards ranges over $\mathcal R$. A single action type is used for all states, as the book's footnote 3 (p. 48) allows. There is no terminal state: Chapter 4 is formalized for continuing tasks with discount $\gamma < 1$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; §3.5, p. 58; opening of Ch. 4, p. 73

import Mathlib

namespace SuttonBartoRL.DP

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49, and the opening of Chapter 4, p. 73: a finite Markov decision process with finite state
set `S`, one finite action set `A` for every state (footnote 3, p. 48), a finite reward set `R ⊂ ℝ`,
and four-argument dynamics `p s a s' r = p(s', r | s, a)`, a probability distribution over
`(s', r) ∈ S × R` for every `(s, a)`. Values of `p` at rewards outside `R` are never used. -/
structure MDP (S A : Type) [Fintype S] [Fintype A] where
  /-- The finite reward set `R`. -/
  R : Finset ℝ
  /-- The dynamics `p(s', r | s, a)`, written `p s a s' r`. -/
  p : S → A → S → ℝ → ℝ
  /-- Probabilities are nonnegative. -/
  p_nonneg : ∀ s a s' r, 0 ≤ p s a s' r
  /-- (3.3): `Σ_{s' ∈ S} Σ_{r ∈ R} p(s', r | s, a) = 1` for all `s`, `a`. -/
  p_sum : ∀ s a, ∑ s', ∑ r ∈ R, p s a s' r = 1

namespace MDP

variable {S A : Type} [Fintype S] [Fintype A]

/-- (3.4), p. 49: the state-transition probability `p(s' | s, a) = Σ_{r ∈ R} p(s', r | s, a)`. -/
def trans (M : MDP S A) (s : S) (a : A) (s' : S) : ℝ :=
  ∑ r ∈ M.R, M.p s a s' r

/-- (3.5), p. 49: the expected reward `r(s, a) = Σ_{r ∈ R} r Σ_{s' ∈ S} p(s', r | s, a)`. -/
def expReward (M : MDP S A) (s : S) (a : A) : ℝ :=
  ∑ r ∈ M.R, r * ∑ s', M.p s a s' r

end MDP

/-- §3.5, p. 58: a (stationary, stochastic) policy, `π(a | s)` = `π.prob s a`, a probability
distribution over the actions for each state. -/
structure Policy (S A : Type) [Fintype A] where
  /-- The probability `π(a | s)` of selecting `a` in state `s`. -/
  prob : S → A → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ s a, 0 ≤ prob s a
  /-- For each state the probabilities sum to one. -/
  sum_one : ∀ s, ∑ a, prob s a = 1

namespace Policy

variable {S A : Type} [Fintype A] [DecidableEq A]

/-- A deterministic policy `π : S → A` (§3.5, p. 58; §4.2, p. 78), viewed as the stochastic policy
that selects `π(s)` with probability one: `π(a | s) = 1` if `a = π(s)` and `0` otherwise. -/
def ofDet (d : S → A) : Policy S A where
  prob s a := if a = d s then 1 else 0
  nonneg s a := by split_ifs <;> norm_num
  sum_one s := by simp

end Policy

end SuttonBartoRL.DP


