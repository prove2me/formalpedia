-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Sigma5
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Sigma5
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:19:24.5358+00:00
-- url     : https://prove2.me/theorems/c0bb1f4f-9828-4cdf-b70e-4d7f95a97135
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Sigma5
-- statement:
--   The fifth-power divisor sum. Its value at zero is unused in coefficient formulas.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- The fifth-power divisor sum. Its value at zero is unused in coefficient formulas. -/
def ch12Sigma5 (n : ℕ) : ℤ := ∑ d ∈ Nat.divisors n, (d : ℤ) ^ 5

end RamanujanLostNotebook.PartII


