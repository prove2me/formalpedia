-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_IsFractionalSet
-- name    : ConsensusHalvingItems_Additive_IsFractionalSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:18.452736+00:00
-- url     : https://prove2.me/theorems/8466cd47-233a-4334-8c7d-60e52eb81ef6
-- title:
--   Fractional set of items
-- statement:
--   There are $m$ items. A **fractional set of items** contains a fraction $x_j \in [0,1]$ of each item $j$; it is described by the vector $x = (x_1, \dots, x_m)$ with
--
--   $$
--   0 \le x_j \le 1 \qquad \text{for every item } j .
--   $$
--
--   Fractional sets are the parts of the partitions considered in consensus halving.
--
--   **Formalization Note** Items are `Fin m` (0-based) and the fractions are rationals.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, §2, p. 4 ("A fractional set of items contains a fraction xj ∈ [0, 1] of each item j")

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **Fractional set of items.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, §2, p. 4: "A fractional set of items contains a fraction xj ∈ [0, 1] of
each item j."

A vector `x : Fin m → ℚ` is a fractional set of the items `0, …, m - 1` when every entry lies in
the closed unit interval: `0 ≤ x j ≤ 1` for every `j`.

**Formalization Note.** Items are 0-based (`Fin m` for the paper's `[m]`); fractions are
rational, the values an algorithm can output (Reading 2 of the mission). -/
def IsFractionalSet {m : ℕ} (x : Fin m → ℚ) : Prop := ∀ j, 0 ≤ x j ∧ x j ≤ 1

end ConsensusHalvingItems.Additive


