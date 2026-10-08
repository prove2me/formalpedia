-- Prove2me | Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
-- name    : SuttonBartoRL_FiniteMDP_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:09:34.214993+00:00
-- url     : https://prove2.me/theorems/d3a50133-b6e7-48e3-af4d-2b7eee4e263c
-- title:
--   Finite MDP with four-argument dynamics $p(s', r \mid s, a)$, stochastic policies, and the discounted return
-- statement:
--   This file fixes the model of Chapter 3 of Sutton and Barto's *Reinforcement Learning: An Introduction*.
--
--   1. A **finite Markov decision process** consists of a finite set of states $\mathcal S$, a finite set of actions $\mathcal A$ (the same set in every state), a finite set of rewards $\mathcal R \subset \mathbb R$, and the **dynamics**
--   $$p(s', r \mid s, a) = \Pr\{S_t = s', R_t = r \mid S_{t-1} = s, A_{t-1} = a\},$$
--   a nonnegative function with $\sum_{s' \in \mathcal S}\sum_{r \in \mathcal R} p(s', r \mid s, a) = 1$ for every state $s$ and action $a$ (Eqs. (3.2)–(3.3)).
--   2. The derived **state-transition probabilities** $p(s' \mid s, a) = \sum_{r \in \mathcal R} p(s', r \mid s, a)$ (3.4) and **expected rewards** $r(s, a) = \sum_{r \in \mathcal R} r \sum_{s'} p(s', r \mid s, a)$ (3.5).
--   3. The MDP obtained by **adding a constant $c$ to every reward**: its reward set is $\{r + c : r \in \mathcal R\}$ and its dynamics are $p'(s', r + c \mid s, a) = p(s', r \mid s, a)$ (the operation of Exercise 3.15).
--   4. A **policy** $\pi$, a map giving for every state $s$ a probability distribution $\pi(a \mid s)$ over the actions (§3.5).
--   5. The **discounted return** of a reward sequence $R_1, R_2, \dots$ at time $t$,
--   $$G_t = \sum_{k=0}^{\infty} \gamma^k R_{t+k+1} \qquad (3.8).$$
--
--   These objects are shared by every theorem of the mission.
--
--   **Formalization Note** The book writes $\mathcal A(s)$ and allows, in its footnote 3, a single action set $\mathcal A$; the formalization uses one action set. Values of $p$ at rewards outside $\mathcal R$ are never read. The return is a real series sum (`tsum`), which Lean sets to $0$ when the series diverges; every theorem that uses it assumes bounded rewards and $0 \le \gamma < 1$, where the series converges.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; footnote 3, p. 48; Eq. (3.8), p. 55; §3.5, p. 58; Exercise 3.15, p. 61

import Mathlib

namespace SuttonBartoRL.FiniteMDP

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

/-- Exercise 3.15, p. 61: the MDP obtained by adding a constant `c` to every reward. The reward
set becomes `R + c = {r + c : r ∈ R}` and `p'(s', r | s, a) = p(s', r − c | s, a)`, so that
`p'(s', r + c | s, a) = p(s', r | s, a)`. -/
def shiftRewards (M : MDP S A) (c : ℝ) : MDP S A where
  R := M.R.map (addRightEmbedding c)
  p s a s' r := M.p s a s' (r - c)
  p_nonneg s a s' r := M.p_nonneg s a s' (r - c)
  p_sum s a := by simpa [Finset.sum_map] using M.p_sum s a

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

/-- (3.8), p. 55: the discounted return `G_t = Σ_{k=0}^∞ γ^k R_{t+k+1}` of a reward sequence
`R_1, R_2, …` (given as `R : ℕ → ℝ`, the value `R 0` is not used by `G_t` for `t ≥ 0`). A real
`tsum`, which is `0` when the series is not summable; the theorems use it for bounded rewards and
`0 ≤ γ < 1`, where it converges. -/
noncomputable def discountedReturn (γ : ℝ) (R : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' k : ℕ, γ ^ k * R (t + k + 1)

end SuttonBartoRL.FiniteMDP


