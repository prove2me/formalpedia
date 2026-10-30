-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Inverse
-- name    : RamanujanLostNotebook_PartII_ch11_ch11Inverse
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:23:29.583193+00:00
-- url     : https://prove2.me/theorems/e16b27ed-9b2b-4243-b970-7268767af1e4
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11Inverse
-- statement:
--   Least nonnegative inverse of d modulo c, selected by a finite sum. On the
--   representative locus c>=2 and gcd(c,d)=1 there is precisely one such inverse.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Least nonnegative inverse of d modulo c, selected by a finite sum. On the
representative locus c>=2 and gcd(c,d)=1 there is precisely one such inverse. -/
def ch11Inverse (c d : ℕ) : ℕ :=
  ∑ a ∈ Finset.range c, if (a * d) % c = 1 then a else 0

end RamanujanLostNotebook.PartII

end


