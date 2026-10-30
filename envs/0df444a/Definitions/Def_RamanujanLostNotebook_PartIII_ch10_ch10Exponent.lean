-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Exponent
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Exponent
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:26:58.005528+00:00
-- url     : https://prove2.me/theorems/1b527170-fd59-4f92-abe0-003dd7ee07b9
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Exponent
-- statement:
--   Floor exponent in (10.60.311), for s,e>0 and a prime p. The floor is nonnegative because the quotient inside the logarithm exceeds one.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Floor exponent in (10.60.311), for s,e>0 and a prime p. The floor is nonnegative because the quotient inside the logarithm exceeds one. -/
noncomputable def ch10Exponent (s e : ℝ) (p : ℕ) : ℕ :=
  Nat.floor (Real.log ((Real.rpow (p : ℝ) e - Real.rpow (p : ℝ) (-s)) /
    (Real.rpow (p : ℝ) e - 1)) / (s * Real.log p))

end RamanujanLostNotebook.PartIII

end


