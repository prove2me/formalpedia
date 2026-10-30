-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6MainNum
-- name    : RamanujanLostNotebook_PartI_ch06_ch6MainNum
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:49:56.275792+00:00
-- url     : https://prove2.me/theorems/40f5389a-ca9f-4d43-87af-cc5a0aff9757
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6MainNum
-- statement:
--   The n-th partial numerator in (6.2.2), for n≥1: aq^j+λq^(2j−1) at n=2j−1 and bq^j+λq^(2j) at n=2j. Index zero is unused by continuants.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The n-th partial numerator in (6.2.2), for n≥1: aq^j+λq^(2j−1) at n=2j−1 and bq^j+λq^(2j) at n=2j. Index zero is unused by continuants. -/
def ch6MainNum (a b l q : ℂ) (n : ℕ) : ℂ :=
  (if n % 2 = 1 then a * q ^ ((n + 1) / 2) else b * q ^ (n / 2)) + l * q ^ n

end RamanujanLostNotebook.PartI

end


