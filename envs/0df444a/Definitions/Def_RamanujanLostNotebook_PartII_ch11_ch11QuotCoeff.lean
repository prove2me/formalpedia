-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11QuotCoeff
-- name    : RamanujanLostNotebook_PartII_ch11_ch11QuotCoeff
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:24:25.348992+00:00
-- url     : https://prove2.me/theorems/35a14ed5-ad57-48f8-8680-c7a3144804a5
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11QuotCoeff
-- statement:
--   Exact degree-n coefficient of A/D when D has constant term 1. Each caller supplies
--   polynomials equal to the source numerator and denominator through degree n.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Inv

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Exact degree-n coefficient of A/D when D has constant term 1. Each caller supplies
polynomials equal to the source numerator and denominator through degree n. -/
noncomputable def ch11QuotCoeff (A D : Polynomial ℤ) (n : ℕ) : ℤ :=
  (A * ch11Inv D n).coeff n

end RamanujanLostNotebook.PartII

end


