-- Prove2me | Definitions.Def_SuttonBartoRL_OffPolicy_MDP
-- name    : SuttonBartoRL_OffPolicy_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:21:07.505782+00:00
-- url     : https://prove2.me/theorems/203d9492-fe20-4bed-9720-658260b6205c
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
--   A **policy** assigns to every state $s$ a probability distribution $\pi(a\mid s)$ over actions. In Chapter 11 two policies appear: the **target policy** $\pi$, whose value function is sought, and the **behavior policy** $b$, which generates the data. A **Markov reward process** is the special case of a single action.
--
--   These are the objects on which the off-policy results of Chapter 11 are stated.
--
--   **Formalization Note** The dynamics are a function `p s a s' r` on $\mathcal S \times \mathcal A \times \mathcal S \times \mathbb R$; its values at rewards outside the finite set $\mathcal R$ are never used, since every sum over rewards ranges over $\mathcal R$. A single action type is used for all states, as the book's footnote 3 (p. 48) allows.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; §3.5, p. 58; Ch. 11 opening, p. 257; footnote 3, p. 274

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49: a finite Markov decision process with finite state set `S`, one finite action set `A`
for every state (footnote 3, p. 48), a finite reward set `R ⊂ ℝ`, and four-argument dynamics
`p s a s' r = p(s', r | s, a)`, a probability distribution over `(s', r) ∈ S × R` for every
`(s, a)`. Values of `p` at rewards outside `R` are never used. A Markov reward process (p. 274,
footnote 3) is the special case of a single action. -/
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

end SuttonBartoRL.OffPolicy


