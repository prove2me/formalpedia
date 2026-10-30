-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch09_ch09ResidueTerm
-- name    : RamanujanLostNotebook_PartIII_ch09_ch09ResidueTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:58:51.30226+00:00
-- url     : https://prove2.me/theorems/8305f8b3-2e0e-4528-96ab-3262025ac2ce
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 9: ch09ResidueTerm
-- statement:
--   A term of the residue-r inner series in (9.1.1). Fractional powers use
--   Complex.cpow, hence the individual principal logarithms of a and b. The
--   corresponding square root of ab is a^(1/2)b^(1/2), not an independently chosen
--   principal root of the product. Zero bases are allowed, with exponent zero
--   returning one; all selected exponents are nonnegative.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 9.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- A term of the residue-r inner series in (9.1.1). Fractional powers use
Complex.cpow, hence the individual principal logarithms of a and b. The
corresponding square root of ab is a^(1/2)b^(1/2), not an independently chosen
principal root of the product. Zero bases are allowed, with exponent zero
returning one; all selected exponents are nonnegative. -/
def ch09ResidueTerm (n r : ℕ) (a b : ℂ) (k : ℤ) : ℂ :=
  if k % (n : ℤ) = (r : ℤ) then
    a ^ (((k * (k + 1) : ℤ) : ℂ) / (2 * (n : ℂ))) *
    b ^ (((k * (k - 1) : ℤ) : ℂ) / (2 * (n : ℂ)))
  else 0

end RamanujanLostNotebook.PartIII

end


