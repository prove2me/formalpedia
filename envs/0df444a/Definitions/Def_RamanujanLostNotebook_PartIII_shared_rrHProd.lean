-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrHProd
-- name    : RamanujanLostNotebook_PartIII_shared_rrHProd
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:24:33.367725+00:00
-- url     : https://prove2.me/theorems/d71d055d-6cde-4e1b-9c7c-7c37a0c47720
-- title:
--   Ramanujan's Lost Notebook Part III, shared: rrHProd
-- statement:
--   `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)`, the PRODUCT by which Chapter 2 defines `H(q)` ((2.1.12),
--   p. 10; it enters `A(q)`, `C(q)`, `D(q)` of (2.1.7), (2.1.9), (2.1.10)).  Its equality with the
--   series `rrH q` is the second Rogers–Ramanujan identity, a theorem.
--
--   Domain: `‖q‖ < 1`, where both infinite products converge absolutely and are nonzero, so the
--   quotient is the classical value.
--   Totalization: for `‖q‖ ≥ 1` the products take Mathlib's junk values and a zero denominator
--   gives `1 / 0 = 0`; never the book's object.  `rrHProd 0 = 1`.
--   Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
--   `rrHProd (1/5) = 1.0500833387096912048…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)`, the PRODUCT by which Chapter 2 defines `H(q)` ((2.1.12),
p. 10; it enters `A(q)`, `C(q)`, `D(q)` of (2.1.7), (2.1.9), (2.1.10)).  Its equality with the
series `rrH q` is the second Rogers–Ramanujan identity, a theorem.

Domain: `‖q‖ < 1`, where both infinite products converge absolutely and are nonzero, so the
quotient is the classical value.
Totalization: for `‖q‖ ≥ 1` the products take Mathlib's junk values and a zero denominator
gives `1 / 0 = 0`; never the book's object.  `rrHProd 0 = 1`.
Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
`rrHProd (1/5) = 1.0500833387096912048…`. -/
def rrHProd (q : ℂ) : ℂ :=
  1 / (qPochInf (q ^ 2) (q ^ 5) * qPochInf (q ^ 3) (q ^ 5))

end RamanujanLostNotebook.PartIII

end


