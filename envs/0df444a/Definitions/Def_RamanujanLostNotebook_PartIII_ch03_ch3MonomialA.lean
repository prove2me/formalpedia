-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3MonomialA
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3MonomialA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:01:17.746404+00:00
-- url     : https://prove2.me/theorems/f814571d-29cc-4a42-bd4e-cc63db61b861
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3MonomialA
-- statement:
--   The Laurent monomial a^k in the integer group algebra Z[Z]=Z[a,a⁻¹].
--   Multiplication adds integer exponents; negative powers are units, not division.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- The Laurent monomial a^k in the integer group algebra Z[Z]=Z[a,a⁻¹].
Multiplication adds integer exponents; negative powers are units, not division. -/
def ch3MonomialA (k : ℤ) : AddMonoidAlgebra ℤ ℤ :=
  AddMonoidAlgebra.single k (1 : ℤ)

end RamanujanLostNotebook.PartIII

end


