-- Prove2me | Definitions.Def_RamanujanNotebooks_ch01_ch1DiagSum
-- name    : RamanujanNotebooks_ch01_ch1DiagSum
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:11:00.251054+00:00
-- url     : https://prove2.me/theorems/2bd15b40-070a-4059-ab4a-2a721199262d
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 1: ch1DiagSum
-- statement:
--   Sum of the main diagonal `M 0 0 + M 1 1 + ⋯ + M (n-1) (n-1)` of an `n × n` array of
--   natural numbers (rows indexed first, top to bottom; columns second, left to right).
--   A finite sum: no domain restriction, no junk value.
--   Reference: for `![![6, 1, 8], ![7, 5, 3], ![2, 9, 4]]` the value is `6 + 5 + 4 = 15`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1.

import Mathlib

namespace RamanujanNotebooks

/-- Sum of the main diagonal `M 0 0 + M 1 1 + ⋯ + M (n-1) (n-1)` of an `n × n` array of
natural numbers (rows indexed first, top to bottom; columns second, left to right).
A finite sum: no domain restriction, no junk value.
Reference: for `![![6, 1, 8], ![7, 5, 3], ![2, 9, 4]]` the value is `6 + 5 + 4 = 15`. -/
def ch1DiagSum {n : ℕ} (M : Fin n → Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, M i i

end RamanujanNotebooks


