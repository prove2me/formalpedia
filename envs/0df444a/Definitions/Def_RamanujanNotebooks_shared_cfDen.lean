-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_cfDen
-- name    : RamanujanNotebooks_shared_cfDen
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T03:04:19.29431+00:00
-- url     : https://prove2.me/theorems/876760aa-d80a-4ec8-a18f-085feb5fff5e
-- title:
--   Ramanujan's Notebooks, shared: cfDen
-- statement:
--   Denominator `B_n` of the `n`-th convergent of the continued fraction
--   `b 0 + a 0 / (b 1 + a 1 / (b 2 + a 2 / (b 3 + ⋯)))` with partial numerators `a 0, a 1, …` and
--   partial denominators `b 0, b 1, …` (complex sequences), by the usual three-term recurrence
--   `B_0 = 1`, `B_1 = b 1`, `B_{n+2} = b (n+2) * B_{n+1} + a (n+1) * B_n`.
--   Used for the continued fractions of Part III, Chapter 16, Entries 10–13 (pp. 19–28).
--   No division occurs: the function is total, with no junk value; `b 0` is not used.
--   Whether `B_n ≠ 0` is a matter for each statement.
--   Reference: for `a k = k + 1`, `b k = 2k + 1` the values at `n = 0, 1, 2, 3` are
--   `1, 3, 17, 128` (so the third convergent of `1 + 1/(3 + 2/(5 + 3/7))` is `166/128`).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

namespace RamanujanNotebooks

/-- Denominator `B_n` of the `n`-th convergent of the continued fraction
`b 0 + a 0 / (b 1 + a 1 / (b 2 + a 2 / (b 3 + ⋯)))` with partial numerators `a 0, a 1, …` and
partial denominators `b 0, b 1, …` (complex sequences), by the usual three-term recurrence
`B_0 = 1`, `B_1 = b 1`, `B_{n+2} = b (n+2) * B_{n+1} + a (n+1) * B_n`.
Used for the continued fractions of Part III, Chapter 16, Entries 10–13 (pp. 19–28).
No division occurs: the function is total, with no junk value; `b 0` is not used.
Whether `B_n ≠ 0` is a matter for each statement.
Reference: for `a k = k + 1`, `b k = 2k + 1` the values at `n = 0, 1, 2, 3` are
`1, 3, 17, 128` (so the third convergent of `1 + 1/(3 + 2/(5 + 3/7))` is `166/128`). -/
noncomputable def cfDen (a b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => b 1
  | (n + 2) => b (n + 2) * cfDen a b (n + 1) + a (n + 1) * cfDen a b n

end RamanujanNotebooks


