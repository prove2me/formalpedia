-- Prove2me | Definitions.Def_IntroDelayAMDP_bonusIter
-- name    : IntroDelayAMDP_bonusIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:23.133991+00:00
-- url     : https://prove2.me/theorems/cb913901-ff4f-46d4-9222-bf35ee067399
-- title:
--   Optimistic backward iteration
-- statement:
--   For a set $\mathcal P$ of transitions, a policy $\pi$ and a bonus $b$: $B_0\equiv0$ and
--   $$B_{n+1}(s,a)=b(s)+\sup_{P'\in\mathcal P}\sum_{s'}P'(s'\mid s,a)\sum_{a'}\pi(a'\mid s')B_n(s',a').$$
--
--   **Formalization Note** The supremum is a real supremum over the subtype of $\mathcal P$. For a nonempty set of transitions the inner sums are bounded, so it is genuine.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (18), p.16

import Mathlib

namespace IntroDelayAMDP

/-- **Optimistic backward iteration** (auxiliary for Eq. (18), p.16). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.16, Eq. (18).

`bonusIter cs π b n s a` is `0` for `n = 0`, and for `n + 1` it is
`b(s) + sup_{P′∈cs} ∑_{s′} P′(s′ | s, a) ∑_{a′} π(a′ | s′) · bonusIter cs π b n s′ a′`.

**Formalization Note.** The supremum is `⨆` over the subtype of `cs`; for a nonempty set of
transitions the inner sums are bounded (rows are probability vectors), so it is the genuine
supremum. -/
noncomputable def bonusIter {St A : Type} [Fintype St] [Fintype A]
    (cs : Set (St → A → St → ℝ)) (π : St → A → ℝ) (b : St → ℝ) : ℕ → St → A → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun s a =>
      b s + ⨆ P' : cs, ∑ s', (P' : St → A → St → ℝ) s a s' * ∑ a', π s' a' * bonusIter cs π b n s' a'

end IntroDelayAMDP


