-- Prove2me | Definitions.Def_SuttonBartoRL_LinearTD_MDP
-- name    : SuttonBartoRL_LinearTD_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:10:50.376982+00:00
-- url     : https://prove2.me/theorems/7f070c98-7827-46a4-b32b-2b62ea6f5fce
-- title:
--   Finite MDP with dynamics $p(s', r \mid s, a)$, stochastic policies, the induced chain and the true value function $v_\pi$
-- statement:
--   This file fixes the model on which Chapter 9 of Sutton and Barto's *Reinforcement Learning: An Introduction* evaluates a policy.
--
--   1. A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same set in every state), a finite set of rewards $\mathcal R \subset \mathbb R$, and the **dynamics** $p(s', r \mid s, a)$, a nonnegative function with $\sum_{s' \in \mathcal S}\sum_{r \in \mathcal R} p(s', r \mid s, a) = 1$ for every state $s$ and action $a$ (Eqs. (3.2)–(3.3)).
--   2. The derived **state-transition probabilities** $p(s' \mid s, a) = \sum_{r} p(s', r \mid s, a)$ (3.4) and **expected rewards** $r(s, a) = \sum_{r} r \sum_{s'} p(s', r \mid s, a)$ (3.5).
--   3. A **policy** $\pi$, giving for every state $s$ a probability distribution $\pi(a \mid s)$ over the actions.
--   4. The Markov chain that $\pi$ induces on the states: its **transition matrix** $P$, the $|\mathcal S| \times |\mathcal S|$ matrix with entries
--   $$P(s, s') = p(s' \mid s) = \sum_a \pi(a \mid s)\, p(s' \mid s, a),$$
--   and its **expected one-step reward** $r_\pi(s) = \sum_a \pi(a \mid s)\, r(s, a)$.
--   5. The **true value function** of $\pi$ with discount rate $\gamma$, the expected discounted return (3.12),
--   $$v_\pi(s) = \mathbb E_\pi\Big[\sum_{k=0}^\infty \gamma^k R_{t+k+1} \,\Big|\, S_t = s\Big] = \sum_{k=0}^\infty \gamma^k (P^k r_\pi)(s).$$
--
--   These objects are the $v_\pi$, $p(s' \mid s)$ and $P$ of Section 9.4 and its box "Proof of Convergence of Linear TD(0)".
--
--   **Formalization Note** The book writes $\mathcal A(s)$ and allows, in its footnote 3 (p. 48), a single action set $\mathcal A$; the formalization uses one action set. Values of $p$ at rewards outside $\mathcal R$ are never read. The value function is defined from expected returns, not as the solution of a Bellman equation; it is a real series (`tsum`), which Lean sets to $0$ when the series diverges, and every theorem that uses it assumes $0 \le \gamma < 1$, where it converges absolutely.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; §3.5 and Eq. (3.12), p. 58; box "Proof of Convergence of Linear TD(0)", pp. 206–207

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.LinearTD

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

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- (3.4), p. 49: the state-transition probability `p(s' | s, a) = Σ_{r ∈ R} p(s', r | s, a)`. -/
def trans (M : MDP S A) (s : S) (a : A) (s' : S) : ℝ :=
  ∑ r ∈ M.R, M.p s a s' r

/-- (3.5), p. 49: the expected reward `r(s, a) = Σ_{r ∈ R} r Σ_{s' ∈ S} p(s', r | s, a)`. -/
def expReward (M : MDP S A) (s : S) (a : A) : ℝ :=
  ∑ r ∈ M.R, r * ∑ s', M.p s a s' r

/-- p. 206: the state-transition matrix `P` of the Markov chain induced by `π`,
`P(s, s') = p(s' | s) = Σ_a π(a | s) p(s' | s, a)`, "the probability of transition from `s` to `s'`
under policy `π`". -/
def policyTrans (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- `E_π[R_{t+k+1} | S_t = s] = (P^k r_π)(s)`: the expected reward `k + 1` steps after starting in
`s` and following `π`. -/
def expectedRewardAt (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (k : ℕ) : S → ℝ :=
  Matrix.mulVec (policyTrans M π ^ k) (policyReward M π)

/-- (3.12), p. 58: the true state-value function
`v_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P^k r_π)(s)`,
defined from expected returns, not from a Bellman equation. A real `tsum`; the theorems take
`0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * expectedRewardAt M π k s

end MDP

end SuttonBartoRL.LinearTD


