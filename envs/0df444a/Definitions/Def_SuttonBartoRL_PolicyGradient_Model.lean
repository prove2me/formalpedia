-- Prove2me | Definitions.Def_SuttonBartoRL_PolicyGradient_Model
-- name    : SuttonBartoRL_PolicyGradient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:55:51.472983+00:00
-- url     : https://prove2.me/theorems/79d3a31b-8a03-41b5-a4ad-fbb423efebe4
-- title:
--   Finite episodic and continuing MDPs with dynamics $p(s', r \mid s, a)$, and differentiable policy parameterizations $\pi(a \mid s, \theta)$
-- statement:
--   This file fixes the three objects on which Chapter 13 is stated.
--
--   1. A **finite episodic MDP** has a finite set $\mathcal S$ of nonterminal states, one terminal state (so that $\mathcal S^+ = \mathcal S \cup \{\text{terminal}\}$), a finite action set $\mathcal A$, a finite reward set $\mathcal R \subset \mathbb R$, and dynamics
--   $$
--   p(s', r \mid s, a) \ge 0, \qquad \sum_{s' \in \mathcal S^+} \sum_{r \in \mathcal R} p(s', r \mid s, a) = 1 \qquad (s \in \mathcal S,\ a \in \mathcal A).
--   $$
--   The terminal state is absorbing and yields only zero rewards. Derived from $p$ are the probability $p(s' \mid s, a) = \sum_{r} p(s', r \mid s, a)$ of moving to a **nonterminal** state $s'$ (3.4) (these sum to at most one over $s' \in \mathcal S$; the remainder is the probability of terminating) and the expected reward $r(s,a) = \sum_{r} r \sum_{s' \in \mathcal S^+} p(s', r \mid s, a)$ (3.5).
--   2. A **finite continuing MDP** is the same without a terminal state: $\sum_{s' \in \mathcal S} \sum_{r} p(s', r \mid s, a) = 1$, with $p(s' \mid s,a)$ and $r(s,a)$ as in (3.4)–(3.5).
--   3. A **differentiable policy parameterization** with parameter $\theta \in \mathbb R^{d'}$ assigns to every $\theta$ and every state $s$ a probability distribution $\pi(\cdot \mid s, \theta)$ over $\mathcal A$, such that for every $s$ and $a$ the map $\theta \mapsto \pi(a \mid s, \theta)$ is differentiable on all of $\mathbb R^{d'}$.
--
--   These are the standing objects of §§13.1–13.2 and 13.6: the policy gradient theorem is a statement about how the value of such a policy depends on $\theta$.
--
--   **Formalization Note** $\mathcal S^+$ is `Option S`, with `none` the terminal state. A single terminal state loses nothing: every terminal state has value $0$ and is never left, so several terminal states can be merged. One action type serves all states (footnote 3, p. 48). The parameter space is `EuclideanSpace ℝ (Fin d)`, so that gradients are vectors of $\mathbb R^{d'}$. Values of `p` at rewards outside the finite set $\mathcal R$ are never used.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.2)–(3.5), pp. 48–49; §3.4, p. 57 (absorbing terminal state); §13.1, p. 322 (differentiable parameterization); §13.2, p. 324; §13.6, p. 333

import Mathlib

namespace SuttonBartoRL.PolicyGradient

/-- Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed. (2018), §3.1, Eqs. (3.2)–(3.3),
pp. 48–49, and §3.4, p. 57, with the episodic setting of §13.2, p. 324: a finite **episodic** MDP.
`S` is the finite set of nonterminal states; the book's `S⁺` is `Option S`, with `none` the terminal
state. `A` is one finite action set for every state (footnote 3, p. 48), `R ⊂ ℝ` a finite reward
set, and `p s a s' r = p(s', r | s, a)` the four-argument dynamics from a nonterminal state `s`,
a probability distribution over `(s', r) ∈ S⁺ × R`. The terminal state is absorbing and yields
only zero rewards (p. 57), so its dynamics are not recorded. Values of `p` at rewards outside `R`
are never used. -/
structure EpisodicMDP (S A : Type) [Fintype S] [Fintype A] where
  /-- The finite reward set `R`. -/
  R : Finset ℝ
  /-- The dynamics `p(s', r | s, a)` for nonterminal `s`; `s' = none` is the terminal state. -/
  p : S → A → Option S → ℝ → ℝ
  /-- Probabilities are nonnegative. -/
  p_nonneg : ∀ s a s' r, 0 ≤ p s a s' r
  /-- (3.3): `Σ_{s' ∈ S⁺} Σ_{r ∈ R} p(s', r | s, a) = 1`. -/
  p_sum : ∀ s a, ∑ s' : Option S, ∑ r ∈ R, p s a s' r = 1

namespace EpisodicMDP

variable {S A : Type} [Fintype S] [Fintype A]

/-- (3.4), p. 49: the probability `p(s' | s, a) = Σ_{r ∈ R} p(s', r | s, a)` of moving to the
nonterminal state `s'`. Summed over `s' ∈ S` it is at most one (the rest is termination). -/
def trans (M : EpisodicMDP S A) (s : S) (a : A) (s' : S) : ℝ :=
  ∑ r ∈ M.R, M.p s a (some s') r

/-- (3.5), p. 49: the expected reward `r(s, a) = Σ_{r ∈ R} r Σ_{s' ∈ S⁺} p(s', r | s, a)`, including
the reward of a transition into the terminal state. -/
def expReward (M : EpisodicMDP S A) (s : S) (a : A) : ℝ :=
  ∑ r ∈ M.R, r * ∑ s' : Option S, M.p s a s' r

end EpisodicMDP

/-- Sutton & Barto (2018), §3.1, Eqs. (3.2)–(3.3), pp. 48–49, with the continuing setting of §10.3,
p. 249, and §13.6, p. 333: a finite **continuing** MDP (no terminal state) with finite state set `S`,
one finite action set `A`, a finite reward set `R ⊂ ℝ`, and dynamics `p s a s' r = p(s', r | s, a)`,
a probability distribution over `(s', r) ∈ S × R`. -/
structure ContinuingMDP (S A : Type) [Fintype S] [Fintype A] where
  /-- The finite reward set `R`. -/
  R : Finset ℝ
  /-- The dynamics `p(s', r | s, a)`. -/
  p : S → A → S → ℝ → ℝ
  /-- Probabilities are nonnegative. -/
  p_nonneg : ∀ s a s' r, 0 ≤ p s a s' r
  /-- (3.3): `Σ_{s' ∈ S} Σ_{r ∈ R} p(s', r | s, a) = 1`. -/
  p_sum : ∀ s a, ∑ s', ∑ r ∈ R, p s a s' r = 1

namespace ContinuingMDP

variable {S A : Type} [Fintype S] [Fintype A]

/-- (3.4), p. 49: `p(s' | s, a) = Σ_{r ∈ R} p(s', r | s, a)`. -/
def trans (M : ContinuingMDP S A) (s : S) (a : A) (s' : S) : ℝ :=
  ∑ r ∈ M.R, M.p s a s' r

/-- (3.5), p. 49: `r(s, a) = Σ_{r ∈ R} r Σ_{s'} p(s', r | s, a)`. -/
def expReward (M : ContinuingMDP S A) (s : S) (a : A) : ℝ :=
  ∑ r ∈ M.R, r * ∑ s', M.p s a s' r

end ContinuingMDP

/-- §13.1, p. 322: a **differentiable policy parameterization** `π(a | s, θ)` with parameter
`θ ∈ ℝ^{d'}` (here `d`), written `π.prob θ s a`. For every `θ` and `s` it is a probability
distribution over the actions, and for every `s, a` the map `θ ↦ π(a | s, θ)` is differentiable
("as long as `∇π(a|s, θ)` … exists and is finite for all `s ∈ S`, `a ∈ A(s)`, and `θ ∈ ℝ^{d'}`"). -/
structure ParamPolicy (S A : Type) [Fintype A] (d : ℕ) where
  /-- `π(a | s, θ)`. -/
  prob : EuclideanSpace ℝ (Fin d) → S → A → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ θ s a, 0 ≤ prob θ s a
  /-- For every `θ` and `s` the action probabilities sum to one. -/
  sum_one : ∀ θ s, ∑ a, prob θ s a = 1
  /-- `θ ↦ π(a | s, θ)` is differentiable on all of `ℝ^{d'}`. -/
  differentiable : ∀ s a, Differentiable ℝ (fun θ => prob θ s a)

end SuttonBartoRL.PolicyGradient


