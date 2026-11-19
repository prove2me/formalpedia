-- Prove2me | Definitions.Def_a166944_B
-- name    : a166944_B
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-19T05:49:57.608846+00:00
-- url     : https://prove2.me/theorems/7ccffc0b-6c92-45aa-a3ca-a2598a763919
-- title:
--   OEIS A166944 - the doubled-index offset $B_n = a_n - (2n-2)$
-- statement:
--   Let $a$ be the OEIS A166944 recurrence. Define the offset from the doubled index by
--
--   $$
--   B_n = a_n - (2n-2).
--   $$
--
--   This is the coordinate in which the terminal argument of the recurrence is stated. Two facts make it the right coordinate. First, at a moving-horizon state $(s,C)$ -- meaning $a_s-s=C$ with $s<C$ -- the ledger
--
--   $$
--   B_s + s = C + 2
--   $$
--
--   holds identically, so $B$ trades off directly against the index: a quiet tail, along which every increment is $1$, decreases $B$ by exactly the length of the tail. Second, the fundamental identity at a terminal exit is $B_{C_f}=2$: the terminal horizon is precisely where the sequence returns to twice its own index.
--
--   Those two facts together are why a capped replay's terminal index can be bounded by $B$, and why the record argument reduces to a statement about this one integer sequence.
--
--   Kept as a separate bundle because the canonical bundle defines $B$ together with the attained-maximum predicate, and importing that bundle into an environment where the predicate already exists would be a name collision.
-- source:
--   Derived within this development; the Mathlib-side original is BCoordinates.B / a166944_canonical. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_record_core

namespace A166944Research

/-- The offset of the A166944 sequence from the doubled index:

    `B n = a n - (2 * n - 2)`.

At a moving-horizon state `(s, C)` the ledger `B s + s = C + 2` holds, which is why
`B` is the coordinate in which the terminal argument is stated: a quiet tail makes
`B` decrease by exactly the tail length, and the fundamental identity at a terminal
exit is `B C_f = 2`.

Kept as its own bundle because the canonical bundle on the Mathlib side defines it
together with `IsAttainedPreviousMaximum`, and importing that bundle into this
environment would collide with the definition already present in
`Def_a166944_moving_horizon`. -/
def B (n : Nat) : Nat := a n - (2 * n - 2)

end A166944Research


