-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch04_ch04Sym
-- name    : RamanujanLostNotebook_PartIII_ch04_ch04Sym
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T07:43:49.377294+00:00
-- url     : https://prove2.me/theorems/05efc861-18ae-4e45-8c2e-a2a948a01f95
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 4: ch04Sym
-- statement:
--   The symmetric Laurent monomial a_n=a^n+a^{-n} of (4.2.3), including a_0=2.
--   The argument a is nonzero in every analytic statement using this definition.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 4.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The symmetric Laurent monomial a_n=a^n+a^{-n} of (4.2.3), including a_0=2.
The argument a is nonzero in every analytic statement using this definition. -/
def ch04Sym (a : ℂ) (n : ℕ) : ℂ := a ^ n + (a⁻¹) ^ n

end RamanujanLostNotebook.PartIII

end


