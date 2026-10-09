-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_cfNum
-- name    : RamanujanNotebooks_shared_cfNum
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T03:04:37.156241+00:00
-- url     : https://prove2.me/theorems/a7ad8fe9-6bc8-4a1b-b002-8275591012fb
-- title:
--   Ramanujan's Notebooks, shared: cfNum
-- statement:
--   Numerator `A_n` of the `n`-th convergent of the continued fraction
--   `b 0 + a 0 / (b 1 + a 1 / (b 2 + a 2 / (b 3 + ⋯)))` with partial numerators `a 0, a 1, …` and
--   partial denominators `b 0, b 1, …` (complex sequences), by the usual three-term recurrence
--   `A_0 = b 0`, `A_1 = b 1 * b 0 + a 0`, `A_{n+2} = b (n+2) * A_{n+1} + a (n+1) * A_n`.
--   Used for the continued fractions of Part III, Chapter 16, Entries 10–13 (pp. 19–28), whose
--   partial denominators are not all `1`.  No division occurs: the function is total, with no
--   junk value.  The `n`-th convergent is the quotient of this numerator by the denominator
--   obtained from the same recurrence with initial values `1`, `b 1` (when that is nonzero).
--   Reference: for `a k = k + 1`, `b k = 2k + 1` the values at `n = 0, 1, 2, 3` are
--   `1, 4, 22, 166`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

namespace RamanujanNotebooks

/-- Numerator `A_n` of the `n`-th convergent of the continued fraction
`b 0 + a 0 / (b 1 + a 1 / (b 2 + a 2 / (b 3 + ⋯)))` with partial numerators `a 0, a 1, …` and
partial denominators `b 0, b 1, …` (complex sequences), by the usual three-term recurrence
`A_0 = b 0`, `A_1 = b 1 * b 0 + a 0`, `A_{n+2} = b (n+2) * A_{n+1} + a (n+1) * A_n`.
Used for the continued fractions of Part III, Chapter 16, Entries 10–13 (pp. 19–28), whose
partial denominators are not all `1`.  No division occurs: the function is total, with no
junk value.  The `n`-th convergent is the quotient of this numerator by the denominator
obtained from the same recurrence with initial values `1`, `b 1` (when that is nonzero).
Reference: for `a k = k + 1`, `b k = 2k + 1` the values at `n = 0, 1, 2, 3` are
`1, 4, 22, 166`. -/
noncomputable def cfNum (a b : ℕ → ℂ) : ℕ → ℂ
  | 0 => b 0
  | 1 => b 1 * b 0 + a 0
  | (n + 2) => b (n + 2) * cfNum a b (n + 1) + a (n + 1) * cfNum a b n

end RamanujanNotebooks


