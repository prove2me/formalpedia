-- Prove2me | Definitions.Def_RamanujanNotebooks_ch01_ch1AntiDiagSum
-- name    : RamanujanNotebooks_ch01_ch1AntiDiagSum
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:11:24.212555+00:00
-- url     : https://prove2.me/theorems/f4154586-d21c-423c-9bfd-5e89dcfa08ff
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 1: ch1AntiDiagSum
-- statement:
--   Sum of the secondary diagonal `M 0 (n-1) + M 1 (n-2) + ⋯ + M (n-1) 0` of an `n × n`
--   array of natural numbers (`Fin.rev i` is the index `n - 1 - i`).
--   A finite sum: no domain restriction, no junk value.
--   Reference: for `![![10, 2, 7], ![4, 6, 9], ![5, 11, 3]]` the value is `7 + 6 + 5 = 18`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1.

import Mathlib

namespace RamanujanNotebooks

/-- Sum of the secondary diagonal `M 0 (n-1) + M 1 (n-2) + ⋯ + M (n-1) 0` of an `n × n`
array of natural numbers (`Fin.rev i` is the index `n - 1 - i`).
A finite sum: no domain restriction, no junk value.
Reference: for `![![10, 2, 7], ![4, 6, 9], ![5, 11, 3]]` the value is `7 + 6 + 5 = 18`. -/
def ch1AntiDiagSum {n : ℕ} (M : Fin n → Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, M i (Fin.rev i)

end RamanujanNotebooks


