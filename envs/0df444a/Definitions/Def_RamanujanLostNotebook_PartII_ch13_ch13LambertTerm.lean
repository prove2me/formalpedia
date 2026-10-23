-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch13_ch13LambertTerm
-- name    : RamanujanLostNotebook_PartII_ch13_ch13LambertTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:41:00.102988+00:00
-- url     : https://prove2.me/theorems/62962d26-541d-439f-a093-e4e4ab691a9a
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 13: ch13LambertTerm
-- statement:
--   The k-th Lambert summand, indexed from k=1 as in (13.1.1)–(13.1.3), p.327.
--   The natural index n denotes k=n+1; the exponent and the cast are explicit.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 13.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The k-th Lambert summand, indexed from k=1 as in (13.1.1)–(13.1.3), p.327.
The natural index n denotes k=n+1; the exponent and the cast are explicit. -/
def ch13LambertTerm (r : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ r * q ^ (n + 1) / (1 - q ^ (n + 1))

end RamanujanLostNotebook.PartII

end


