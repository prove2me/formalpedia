-- Prove2me | Definitions.Def_RvsCert_wY
-- name    : RvsCert_wY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:17.855202+00:00
-- url     : https://prove2.me/theorems/1371359f-4767-40ca-b85a-e446be1bf8ba
-- title:
--   Bit width $w_Y(n)$ of a proposal-card entry
-- statement:
--   A proposal-card entry is a running total, at most $n$ in a valid card. It is stored in
--   $$
--   w_Y(n)=\lfloor\log_2 n\rfloor+1
--   $$
--   bits, so every number up to $2^{w_Y(n)}-1\ge n$ is representable.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2

import Mathlib

namespace RvsCert

/-- **Bit width of a proposal-card entry** (Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1). A card entry
is a running total, a number in `[0, n]` in valid cards, stored in `⌊log₂ n⌋ + 1` bits (so every
value up to `2^{wY n} − 1 ≥ n` is representable). -/
def wY (n : ℕ) : ℕ := Nat.log 2 n + 1

end RvsCert


