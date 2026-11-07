-- Prove2me | Definitions.Def_IntroDelayAMDP_IsTransition
-- name    : IntroDelayAMDP_IsTransition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:30.503783+00:00
-- url     : https://prove2.me/theorems/09c0eb7e-9b40-4a90-a0b0-1eb4dd12e1db
-- title:
--   Transition of a layered AMDP
-- statement:
--   A function $P(s'\mid s,a)$ is a **transition** of the layered space if it is nonnegative, if $P(s'\mid s,a)\neq 0$ only when $s'$ lies in the layer after $s$, and if $\sum_{s'}P(s'\mid s,a)=1$ for every pair $(s,a)$ with $h(s)+1<H$.
--
--   The same predicate describes the true transition and "the set of all transitions" of Algorithm 1, line 1. Since rows must sum to one, every layer $h<H$ is nonempty, so $S\ge H$.
--
--   **Formalization Note** For a pair of the last layer the support clause forces the row to vanish, since its successors are the unmodelled terminal states.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Definition 1.1, p.3; Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace

namespace IntroDelayAMDP

/-- **Transition of a layered AMDP** (Definition 1.1, p.3; Section 2.1, p.12).
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, printed p.12: "`P : S × A → ∆(S ∪ S_H)` is the transition … transitions only
happen from one layer to the next one, that is, `P(· | s, a) ∈ ∆(S_{h+1})` for all `s ∈ S_h` and
`a ∈ A`".

`IsTransition L P` says: `P s a s' ≥ 0`; `P s a s' ≠ 0` only if `s'` lies in the layer after `s`;
and for `s` in a layer `h` with `h + 1 < H`, the row `P(· | s, a)` sums to `1`.

**Formalization Note.** For a pair of the last layer `H − 1`, the successor is a terminal state of
`S_H`, which is not modelled (see `LayeredSpace`): the support clause forces the row to be `0`.
The same predicate is "the set of all transitions" of Algorithm 1, line 1. -/
def IsTransition {St A : Type} [Fintype St] {H : ℕ} (L : LayeredSpace St H)
    (P : St → A → St → ℝ) : Prop :=
  (∀ s a s', 0 ≤ P s a s') ∧ (∀ s a s', P s a s' ≠ 0 → L.layer s' = L.layer s + 1) ∧
    (∀ s a, L.layer s + 1 < H → ∑ s', P s a s' = 1)

end IntroDelayAMDP


