-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrGProd
-- name    : RamanujanLostNotebook_PartIII_shared_rrGProd
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:23:58.925395+00:00
-- url     : https://prove2.me/theorems/1f54975e-c74a-48c1-9dc5-88062ab4aab8
-- title:
--   Ramanujan's Lost Notebook Part III, shared: rrGProd
-- statement:
--   `1 / ((q; q^5)_∞ (q^4; q^5)_∞)`, the PRODUCT by which Chapter 2 defines `G(q)` ((2.1.11),
--   p. 10; it enters `A(q)`, `B(q)`, `D(q)` of (2.1.7), (2.1.8), (2.1.10)).  Its equality with the
--   series `rrG q` is the first Rogers–Ramanujan identity, a theorem.
--
--   Domain: `‖q‖ < 1`, where both infinite products converge absolutely and are nonzero (no
--   factor `1 - q^{5k+1}` or `1 - q^{5k+4}` vanishes), so the quotient is the classical value.
--   Totalization: for `‖q‖ ≥ 1` the products take Mathlib's junk values and a zero denominator
--   gives `1 / 0 = 0`; never the book's object.  `rrGProd 0 = 1`.
--   Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
--   `rrGProd (1/5) = 1.2520840053849600264…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `1 / ((q; q^5)_∞ (q^4; q^5)_∞)`, the PRODUCT by which Chapter 2 defines `G(q)` ((2.1.11),
p. 10; it enters `A(q)`, `B(q)`, `D(q)` of (2.1.7), (2.1.8), (2.1.10)).  Its equality with the
series `rrG q` is the first Rogers–Ramanujan identity, a theorem.

Domain: `‖q‖ < 1`, where both infinite products converge absolutely and are nonzero (no
factor `1 - q^{5k+1}` or `1 - q^{5k+4}` vanishes), so the quotient is the classical value.
Totalization: for `‖q‖ ≥ 1` the products take Mathlib's junk values and a zero denominator
gives `1 / 0 = 0`; never the book's object.  `rrGProd 0 = 1`.
Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
`rrGProd (1/5) = 1.2520840053849600264…`. -/
def rrGProd (q : ℂ) : ℂ :=
  1 / (qPochInf q (q ^ 5) * qPochInf (q ^ 4) (q ^ 5))

end RamanujanLostNotebook.PartIII

end


