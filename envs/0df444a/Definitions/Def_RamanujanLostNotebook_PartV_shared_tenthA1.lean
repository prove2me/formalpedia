-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_tenthA1
-- name    : RamanujanLostNotebook_PartV_shared_tenthA1
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T17:12:29.981172+00:00
-- url     : https://prove2.me/theorems/914a9217-92e8-43f9-8afb-19d17639d503
-- title:
--   Ramanujan's Lost Notebook Part V, shared: tenthA1
-- statement:
--   The theta quotient `a_1(q)` of (9.2.6), p. 186 (the same function is `a_1(q) = a_4(q)` in
--   (9.6.10), p. 198, and `a_1(q)` of (12.1.14), p. 251):
--   `a_1(q) = -q (q^5; q^5)_∞ (q^10; q^10)_∞ f(-q^2, -q^8) / (f(-q, -q^4) f(-q^4, -q^6))`.
--
--   Domain: `‖q‖ < 1`; the two theta functions in the denominator are nonzero there.  Outside:
--   junk of `qPochInf` and `ramanujanTheta`.
--   Reference: `-q - q^2 - 2q^5 - 2q^6 - 2q^7 - 2q^8 - 2q^9 - 3q^10 - …`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_ramanujanTheta

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- The theta quotient `a_1(q)` of (9.2.6), p. 186 (the same function is `a_1(q) = a_4(q)` in
(9.6.10), p. 198, and `a_1(q)` of (12.1.14), p. 251):
`a_1(q) = -q (q^5; q^5)_∞ (q^10; q^10)_∞ f(-q^2, -q^8) / (f(-q, -q^4) f(-q^4, -q^6))`.

Domain: `‖q‖ < 1`; the two theta functions in the denominator are nonzero there.  Outside:
junk of `qPochInf` and `ramanujanTheta`.
Reference: `-q - q^2 - 2q^5 - 2q^6 - 2q^7 - 2q^8 - 2q^9 - 3q^10 - …`. -/
def tenthA1 (q : ℂ) : ℂ :=
  -(q * qPochInf (q ^ 5) (q ^ 5) * qPochInf (q ^ 10) (q ^ 10) *
      ramanujanTheta (-(q ^ 2)) (-(q ^ 8))) /
    (ramanujanTheta (-q) (-(q ^ 4)) * ramanujanTheta (-(q ^ 4)) (-(q ^ 6)))

end RamanujanLostNotebook.PartV

end


