-- Prove2me | Definitions.Def_AggStatePG_Supplement_IsGreedy
-- name    : AggStatePG_Supplement_IsGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:21:53.109493+00:00
-- url     : https://prove2.me/theorems/584d6f75-e87c-4901-a574-dc2798f0e81d
-- title:
--   Greedy policy improvement $\pi(s)\in\arg\max_a\hat Q(s,a)$
-- statement:
--   Given $\hat Q\in\mathbb R^{|\mathcal S|\times|\mathcal A|}$, a deterministic policy $\pi$ is **greedy** with respect to $\hat Q$ if
--   $$\pi(s)\in\arg\max_{a\in\mathcal A}\hat Q(s,a)\qquad\text{for every }s\in\mathcal S.$$
--
--   This is the policy improvement step of approximate policy iteration (Algorithm 1, step (3)) and of soft API (Algorithm 4, step (3)).
--
--   **Formalization Note** A deterministic policy is the table whose row at $s$ is the indicator of the chosen action. The maximizing action is chosen separately at each state, with no tie-breaking rule: every choice the algorithm can make is allowed.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Algorithm 1 step (3), p.12; Algorithm 4 step (3), p.17

import Mathlib

namespace AggStatePG.Supplement

/-- The **greedy policy-improvement step** (Russo, *Approximation Benefits of Policy Gradient Methods
with Aggregated States*, arXiv:2007.11684v3, Algorithm 1 step (3), p.12, and Algorithm 4 step (3),
p.17): `π(s) ∈ argmax_{a ∈ A} Q̂(s,a)` for every `s ∈ S`. `IsGreedy Q̂ π` says that the table `π` is
a deterministic policy that plays, at each state `s`, one action maximizing `Q̂(s, ·)`.

**Formalization Note.** A deterministic policy is a table `π : S → A → ℝ` with `π(s, ·)` the
indicator of the chosen action. The maximizing action is chosen separately at every state (no
tie-breaking rule is fixed): any choice the algorithm may make is allowed. -/
def IsGreedy {S A : Type*} [DecidableEq A] (Q π : S → A → ℝ) : Prop :=
  ∀ s : S, ∃ a : A, (∀ b : A, Q s b ≤ Q s a) ∧ ∀ b : A, π s b = if b = a then 1 else 0

end AggStatePG.Supplement


