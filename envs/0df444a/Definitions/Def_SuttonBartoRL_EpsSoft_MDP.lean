-- Prove2me | Definitions.Def_SuttonBartoRL_EpsSoft_MDP
-- name    : SuttonBartoRL_EpsSoft_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:06:24.167085+00:00
-- url     : https://prove2.me/theorems/969e668d-9977-46ed-9435-a491fd034e25
-- title:
--   A finite MDP with four-argument dynamics p(s′, r | s, a)
-- statement:
--   A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same set in every state, so $|\mathcal A(s)| = |\mathcal A|$), a finite set of rewards $\mathcal R \subset \mathbb R$, and dynamics
--   $$
--   p(s', r \mid s, a) \ge 0, \qquad \sum_{s' \in \mathcal S} \sum_{r \in \mathcal R} p(s', r \mid s, a) = 1 \quad \text{for all } s \in \mathcal S,\ a \in \mathcal A,
--   $$
--   the probability of moving to state $s'$ with reward $r$ after taking action $a$ in state $s$. From it one derives the state-transition probabilities $p(s' \mid s, a) = \sum_{r \in \mathcal R} p(s', r \mid s, a)$ and the expected rewards $r(s, a) = \sum_{r \in \mathcal R} r \sum_{s'} p(s', r \mid s, a)$.
--
--   These are the objects of every dynamic-programming statement of the book; this mission uses them for policy iteration over $\varepsilon$-soft policies. Policies $\pi(a \mid s)$ are the series' shared `SuttonBartoRL.FiniteMDP.Policy`, imported by this file.
--
--   **Formalization Note** The book allows a state-dependent action set $\mathcal A(s)$; following its footnote 3 (p. 48) one action set is used for every state. Values of $p$ at rewards outside $\mathcal R$ are never used.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49, footnote 3 p. 48; policies §3.5, p. 58

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.EpsSoft

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49: a finite Markov decision process with finite state set `S`, one finite action set `A`
for every state (footnote 3, p. 48, so `|A(s)| = Fintype.card A`), a finite reward set `R ⊂ ℝ`, and
four-argument dynamics `p s a s' r = p(s', r | s, a)`, a probability distribution over
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

end SuttonBartoRL.EpsSoft


