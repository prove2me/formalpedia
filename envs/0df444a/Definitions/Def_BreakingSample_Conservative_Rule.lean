-- Prove2me | Definitions.Def_BreakingSample_Conservative_Rule
-- name    : BreakingSample_Conservative_Rule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:32.423709+00:00
-- url     : https://prove2.me/theorems/772b946f-682f-42a0-b6f2-39d053b2a1c2
-- title:
--   (10), p. 8 — the conservative rule π̂c(s) = min{a : Q̂⋆(s,a) > V̂⋆(s) − ς} and the associated value max_a Q(s,a)
-- statement:
--   This module defines the conservative planning rule of Algorithm 2.
--
--   Let the action set be linearly ordered, $\mathcal A = \{1,\dots,|\mathcal A|\}$. Given a Q-function $Q : \mathcal S\times\mathcal A \to \mathbb R$, a value function $V : \mathcal S \to \mathbb R$ and a threshold $\varsigma$, a policy $\pi$ follows the conservative rule when, at every state,
--
--   $$\pi(s) = \min\{a \in \mathcal A : Q(s,a) > V(s) - \varsigma\},$$
--
--   that is, $\pi(s)$ belongs to the set and is below every element of it. With $Q = \widehat Q^\star$, $V = \widehat V^\star$ and $\varsigma \sim \mathrm{Unif}(0,\xi)$ this is the policy $\widehat\pi_{\mathrm c}$ of (10): the smallest-indexed action within $\varsigma$ of optimal in the empirical MDP. The module also defines the associated value function $\widehat V(s) = \max_a \widehat Q(s,a)$ of a Q-function, used in Lemma 8.
--
--   Taking the smallest such action, rather than any action within $\varsigma$ of optimal, is what makes the policy stable under small perturbations of the Q-function.
--
--   **Formalization Note** The rule is a predicate on policies, not a function. For $V = \max_a Q(s,a)$ and $\varsigma > 0$ the set contains a maximizer, so exactly one policy satisfies it; for $\varsigma \le 0$ none does, an event of probability zero under $\mathrm{Unif}(0,\xi)$. Statements about $\widehat\pi_{\mathrm c}$ are written for every policy satisfying the rule. The order of $\mathcal A$ is any linear order on a finite type, which is $\{1,\dots,|\mathcal A|\}$ up to relabelling.
-- source:
--   arXiv:2005.12900v8, §3.1, p. 8, (10); Lemma 8, p. 19

import Mathlib

namespace BreakingSample.Conservative

/-- The associated value function `V̂(s) = max_a Q̂(s,a)` of a Q-function `Q̂` (Lemma 8,
arXiv:2005.12900v8, p. 19). -/
noncomputable def maxQ {S A : Type*} [Fintype A] [Nonempty A] (Q : S → A → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Q s)

/-- The conservative rule (10), arXiv:2005.12900v8, p. 8: `π s` is the smallest action `a` with
`Q(s,a) > V(s) − ς`. -/
def IsConservative {S A : Type*} [LinearOrder A] (Q : S → A → ℝ) (V : S → ℝ) (ς : ℝ) (π : S → A) : Prop :=
  ∀ s, V s - ς < Q s (π s) ∧ ∀ a, V s - ς < Q s a → π s ≤ a

end BreakingSample.Conservative


