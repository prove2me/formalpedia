-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch05_cfNum
-- name    : RamanujanLostNotebook_PartIV_ch05_cfNum
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:51:21.994201+00:00
-- url     : https://prove2.me/theorems/7afbdaac-e519-4587-9b3e-a9fc5106c97d
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 5: cfNum
-- statement:
--   Numerators `U_n` of the continued fraction
--   `b 0 + a 1 / (b 1 + a 2 / (b 2 + a 3 / (b 3 + ⋯)))`, by the recurrence (5.5.3) of the book:
--   `U_0 = b 0`, `U_1 = b 1 * b 0 + a 1`, `U_n = b n * U_{n-1} + a n * U_{n-2}`.
--   (The book starts from `U_{-1} = 1`, `U_0 = b 0`; that gives the same `U_1`.)  The value `a 0`
--   is never used.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 5.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Numerators `U_n` of the continued fraction
`b 0 + a 1 / (b 1 + a 2 / (b 2 + a 3 / (b 3 + ⋯)))`, by the recurrence (5.5.3) of the book:
`U_0 = b 0`, `U_1 = b 1 * b 0 + a 1`, `U_n = b n * U_{n-1} + a n * U_{n-2}`.
(The book starts from `U_{-1} = 1`, `U_0 = b 0`; that gives the same `U_1`.)  The value `a 0`
is never used. -/
def cfNum {K : Type*} [Field K] (a b : ℕ → K) : ℕ → K
  | 0 => b 0
  | 1 => b 1 * b 0 + a 1
  | (n + 2) => b (n + 2) * cfNum a b (n + 1) + a (n + 2) * cfNum a b n

end RamanujanLostNotebook.PartIV


