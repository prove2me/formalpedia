-- Prove2me | Definitions.Def_RvsCert_cardEntry
-- name    : RvsCert_cardEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:27.315204+00:00
-- url     : https://prove2.me/theorems/32fc0477-8db8-4777-95ce-2fd469c6734e
-- title:
--   Decoded proposal-card entry
-- statement:
--   For an input $x$, an athlete $a$ and $j\in\{0,\dots,2n-2\}$, the decoded card entry $Y^a_j$ is the binary value of the $w_Y(n)$ bits of entry $j$ of $a$'s proposal card. In a valid card it is the running total of the non-athletes that beat $a$ in its races $0,\dots,j$.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2

import Mathlib
import Definitions.Def_RvsCert_Idx
import Definitions.Def_RvsCert_bitsVal

namespace RvsCert

/-- **Decoded proposal-card entry** (Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the binary value
of the `wY n` bits of entry `j` of athlete `a`'s card `Y^{a}`, a running total of the
non-athletes that beat `a` in its first `j + 1` races. -/
def cardEntry (n : ℕ) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n) (j : Fin (2 * n - 1)) : ℕ :=
  bitsVal fun t : Fin (wY n) => x (Sum.inr (a, j, t))

end RvsCert


