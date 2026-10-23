-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Upper
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Upper
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:20:47.08698+00:00
-- url     : https://prove2.me/theorems/141117f7-077b-4ab0-8927-6e4cc0b4dee3
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Upper
-- statement:
--   The upper cutoff u(n), p.322. The braces in the display are interpreted
--   as rounding down to an integer, as in the earlier cutoff; the source does not
--   explicitly define these braces. Values n=0,1 are unused.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12PrimeProduct

namespace RamanujanLostNotebook.PartII

/-- The upper cutoff u(n), p.322. The braces in the display are interpreted
as rounding down to an integer, as in the earlier cutoff; the source does not
explicitly define these braces. Values n=0,1 are unused. -/
noncomputable def ch12Upper (epsilon : ℝ) (n : ℕ) : ℕ :=
  Int.toNat ⌊((n : ℝ) * (1 + epsilon)) /
    (Real.rpow (Real.log n) (3 / 2 : ℝ) * Real.sqrt ch12PrimeProduct)⌋

end RamanujanLostNotebook.PartII


