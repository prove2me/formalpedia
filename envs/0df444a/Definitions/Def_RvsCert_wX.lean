-- Prove2me | Definitions.Def_RvsCert_wX
-- name    : RvsCert_wX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:18.400215+00:00
-- url     : https://prove2.me/theorems/b0e6d32e-faeb-476a-9f4a-c6cac059d638
-- title:
--   Bit width $w_X(n)$ of a race-result entry
-- statement:
--   A race-result entry stores either the symbol $\bot$ or one of the $2n^2$ athletes. Coding $\bot$ as $0$ and the athletes as $1,\dots,2n^2$, an entry uses
--   $$
--   w_X(n)=\lceil\log_2(2n^2+1)\rceil
--   $$
--   bits, which is $O(\log n)$, as in the paper's "to encode numbers that represent integers up to n, we use log n bits".
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2

import Mathlib

namespace RvsCert

/-- **Bit width of a race-result entry** (Section 2, p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "to encode
numbers that represent integers up to n, we use log n bits"). An entry stores ⊥ (value `0`) or
one of the `2n²` athletes (values `1, …, 2n²`), so it uses `⌈log₂(2n² + 1)⌉` bits. -/
def wX (n : ℕ) : ℕ := Nat.clog 2 (2 * n ^ 2 + 1)

end RvsCert


