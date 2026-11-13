-- Prove2me | Definitions.Def_RvsCert_claimedPos
-- name    : RvsCert_claimedPos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:43:15.107189+00:00
-- url     : https://prove2.me/theorems/76e6d719-b148-47d9-8045-97c0512091c5
-- title:
--   Claimed finishing position
-- statement:
--   The proposal card of athlete $a$ lists running totals $Y_0,\dots,Y_{2n-2}$. The claimed $0$-based position of $a$ in its $j$-th race is
--   $$
--   p_j=Y_j-Y_{j-1},\qquad Y_{-1}=0,
--   $$
--   the number of non-athletes claimed to finish ahead of $a$ in that race ("the difference of two adjacent entries reveals the corresponding entry", p.2).
--
--   **Formalization Note** Natural-number subtraction, exact whenever the card is non-decreasing, which the champion condition requires.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2

import Mathlib
import Definitions.Def_RvsCert_cardEntry

namespace RvsCert

/-- **Claimed finishing position** (Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: the card holds the
running totals, and "the difference of two adjacent entries reveals the corresponding entry").
The `0`-based position claimed by athlete `a` in its `j`-th race is `Y_j − Y_{j−1}` with
`Y_{−1} = 0` (the number of non-athletes ahead of it).

**Formalization Note.** `ℕ` subtraction; it is exact whenever the card is monotone, which the
champion condition requires. -/
def claimedPos (n : ℕ) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n) (j : Fin (2 * n - 1)) : ℕ :=
  cardEntry n x a j -
    (if h : (j : ℕ) = 0 then 0 else cardEntry n x a ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)

end RvsCert


