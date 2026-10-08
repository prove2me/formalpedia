-- Prove2me | Definitions.Def_SuttonBartoRL_NStep_MDP
-- name    : SuttonBartoRL_NStep_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:18:03.371523+00:00
-- url     : https://prove2.me/theorems/22b2102d-a6b3-4caf-9b4a-f56e6140e5b6
-- title:
--   Finite MDP with dynamics $p(s', r \mid s, a)$, stochastic policies, and the state-value function $v_\pi$
-- statement:
--   This file fixes the model of Chapter 7 of Sutton and Barto's *Reinforcement Learning: An Introduction* (the finite MDP of Chapter 3).
--
--   1. A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same set in every state), a finite set of rewards $\mathcal R \subset \mathbb R$, and the **dynamics** $p(s', r \mid s, a)$, a nonnegative function with $\sum_{s' \in \mathcal S}\sum_{r \in \mathcal R} p(s', r \mid s, a) = 1$ for every state $s$ and action $a$ (Eqs. (3.2)–(3.3)).
--   2. The derived **state-transition probabilities** $p(s' \mid s, a) = \sum_{r \in \mathcal R} p(s', r \mid s, a)$ (3.4) and **expected rewards** $r(s, a) = \sum_{r \in \mathcal R} r \sum_{s'} p(s', r \mid s, a)$ (3.5).
--   3. A **policy** $\pi$, giving for every state $s$ a probability distribution $\pi(a \mid s)$ over the actions (§3.5).
--   4. The transition matrix $P_\pi(s, s') = \sum_a \pi(a \mid s)\, p(s' \mid s, a)$ and the expected one-step reward $r_\pi(s) = \sum_a \pi(a \mid s)\, r(s, a)$ of the Markov chain induced by $\pi$, so that $(P_\pi^k r_\pi)(s) = \mathbb E_\pi[R_{t+k+1} \mid S_t = s]$.
--   5. The **state-value function** (3.12), the expected discounted return from $s$ under $\pi$:
--   $$v_\pi(s) = \mathbb E_\pi\Big[\sum_{k=0}^{\infty} \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] = \sum_{k=0}^{\infty} \gamma^k (P_\pi^k r_\pi)(s).$$
--
--   These objects are shared by every expectation-based theorem of the mission.
--
--   **Formalization Note** The book writes $\mathcal A(s)$ and allows, in its footnote 3 on p. 48, a single action set $\mathcal A$; the formalization uses one action set. The value $v_\pi$ is defined from expected returns, never as the solution of a Bellman equation. It is a real series sum (`tsum`), which Lean sets to $0$ when the series diverges; the theorems that use it assume $0 \le \gamma < 1$, where it converges absolutely. Episodic tasks are represented, as on p. 57, by absorbing terminal states with zero reward.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; footnote 3, p. 48; §3.5 and Eq. (3.12), p. 58

import Mathlib

namespace SuttonBartoRL.NStep

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49: a finite Markov decision process with finite state set `S`, one finite action set `A`
for every state (footnote 3, p. 48), a finite reward set `R ⊂ ℝ`, and four-argument dynamics
`p s a s' r = p(s', r | s, a)`, a probability distribution over `(s', r) ∈ S × R` for every `(s, a)`.
Values of `p` at rewards outside `R` are never used. -/
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

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- `E_π[R_{t+k+1} | S_t = s] = (P_π^k r_π)(s)`: the expected reward `k + 1` steps after starting
in `s` and following `π`. -/
def expectedRewardAt (M : MDP S A) (π : Policy S A) (k : ℕ) : S → ℝ :=
  Matrix.mulVec (policyTrans M π ^ k) (policyReward M π)

/-- (3.12), p. 58: the state-value function
`v_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from the Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

end SuttonBartoRL.NStep


