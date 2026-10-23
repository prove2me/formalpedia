-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertTerm
-- name    : RamanujanLostNotebook_PartII_ch15_ch15LambertTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T07:05:56.22587+00:00
-- url     : https://prove2.me/theorems/8952057a-9f11-4cbc-b11d-1dca6006bd11
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 15: ch15LambertTerm
-- statement:
--   The k-th Lambert summand with positive index r+1, over complex q. P, Q and R use k=1,3,5 (pp.365,367). It is a classical term when |q|<1; no factor 1-q^(r+1) then vanishes.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The k-th Lambert summand with positive index r+1, over complex q. P, Q and R use k=1,3,5 (pp.365,367). It is a classical term when |q|<1; no factor 1-q^(r+1) then vanishes. -/
def ch15LambertTerm (k : ℕ) (q : ℂ) (r : ℕ) : ℂ :=
  ((r + 1 : ℕ) : ℂ) ^ k * q ^ (r + 1) / (1 - q ^ (r + 1))

end RamanujanLostNotebook.PartII

end


