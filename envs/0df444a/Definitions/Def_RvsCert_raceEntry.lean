-- Prove2me | Definitions.Def_RvsCert_raceEntry
-- name    : RvsCert_raceEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:25.152106+00:00
-- url     : https://prove2.me/theorems/a2e75aac-18f7-4083-8e09-f822e7a05cfa
-- title:
--   Decoded race-result entry
-- statement:
--   For an input $x$, a race $r$ and a position $p<n$, the decoded entry $X_r[p]$ is the binary value of the $w_X(n)$ bits stored at position $p$ of the result list of $r$. The value $0$ is $\bot$ (a non-athlete), the value $1+cn+b$ is athlete $(c,b)$, and any other value denotes neither.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, pp.1–2

import Mathlib
import Definitions.Def_RvsCert_Idx
import Definitions.Def_RvsCert_bitsVal

namespace RvsCert

/-- **Decoded race-result entry** (Section 2, p.1–2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "a list X_{c,d}
that stores the race results up to position n"): the binary value of the `wX n` bits of position
`p` of race `r`. Value `0` is ⊥ (a non-athlete), value `athleteCode n a` is athlete `a`, any
other value is neither. -/
def raceEntry (n : ℕ) (x : Idx n → Bool) (r : Race n) (p : Fin n) : ℕ :=
  bitsVal fun t : Fin (wX n) => x (Sum.inl (r, p, t))

end RvsCert


