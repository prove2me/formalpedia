-- Prove2me | Definitions.Def_IntroDelayAMDP_IsPolicy
-- name    : IntroDelayAMDP_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:44.115336+00:00
-- url     : https://prove2.me/theorems/88df3acf-d7bc-47c0-ba1e-8f40e5668275
-- title:
--   Markov policy
-- statement:
--   A **Markov policy** assigns to every state $s$ a probability vector $\pi(\cdot\mid s)$ on the finite action set: $\pi(a\mid s)\ge 0$ and $\sum_a\pi(a\mid s)=1$.
--
--   The comparator policies and the policies played by Algorithm 1 are of this form.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Definition 1.2, p.4; Section 2.1, p.12

import Mathlib

namespace IntroDelayAMDP

/-- **Markov policy** (Definition 1.2, p.4; Section 2.1, p.12). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.12: "A (Markov)
policy `π` of the agent is a mapping from `S` to `∆(A)`".

`IsPolicy π` says that `π s ·` is a probability vector on the finite action set for every state:
`π s a ≥ 0` and `∑ₐ π s a = 1`. The value `π s a` is `π(a | s)`. -/
def IsPolicy {St A : Type} [Fintype A] (π : St → A → ℝ) : Prop :=
  ∀ s, (∀ a, 0 ≤ π s a) ∧ ∑ a, π s a = 1

end IntroDelayAMDP


