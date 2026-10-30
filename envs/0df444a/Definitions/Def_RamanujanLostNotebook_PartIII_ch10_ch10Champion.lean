-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Champion
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Champion
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:33:03.40551+00:00
-- url     : https://prove2.me/theorems/725ce161-c8f5-4379-a460-582c1b8b2cb0
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Champion
-- statement:
--   The canonical superior integer at s,epsilon>0, defined from prime exponents. Only primes not exceeding x_1 occur; larger primes have zero exponent.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Exponent
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Primes
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Threshold

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The canonical superior integer at s,epsilon>0, defined from prime exponents. Only primes not exceeding x_1 occur; larger primes have zero exponent. -/
noncomputable def ch10Champion (s e : ℝ) : ℕ :=
  ∏ p ∈ ch10Primes (ch10Threshold s e 1), p ^ ch10Exponent s e p

end RamanujanLostNotebook.PartIII

end


