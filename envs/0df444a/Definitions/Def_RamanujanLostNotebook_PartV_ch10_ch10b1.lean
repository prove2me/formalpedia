-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch10_ch10b1
-- name    : RamanujanLostNotebook_PartV_ch10_ch10b1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T18:44:26.22102+00:00
-- url     : https://prove2.me/theorems/8c841ff3-ed05-4977-989f-a059bd5752d8
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 10: ch10b1
-- statement:
--   The theta quotient `b_1(q)` of (10.2.3), p. 208 (repeated as (10.6.12), p. 220, where the
--   book also sets `b_4 = -b_1`):
--   `b_1(q) = -(q^5; q^5)_∞ (q^10; q^10)_∞ f(-q^2, -q^3) / (f(-q^2, -q^8) f(-q, -q^4))`.
--   It is the analogue of, and a different function from, `a_1(q)` of (9.2.6).
--
--   Domain: `‖q‖ < 1`; the two theta functions in the denominator are nonzero there.  Outside:
--   junk of `qPochInf` and `ramanujanTheta`.
--   Reference: `-1 - q - q^2 - q^4 - q^6 + q^7 - q^8 - q^10 + q^11 - 2q^12 - …`,
--   `b_1(1/5) = -1.2416538502159946385…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_ramanujanTheta

namespace RamanujanLostNotebook.PartV

/-- The theta quotient `b_1(q)` of (10.2.3), p. 208 (repeated as (10.6.12), p. 220, where the
book also sets `b_4 = -b_1`):
`b_1(q) = -(q^5; q^5)_∞ (q^10; q^10)_∞ f(-q^2, -q^3) / (f(-q^2, -q^8) f(-q, -q^4))`.
It is the analogue of, and a different function from, `a_1(q)` of (9.2.6).

Domain: `‖q‖ < 1`; the two theta functions in the denominator are nonzero there.  Outside:
junk of `qPochInf` and `ramanujanTheta`.
Reference: `-1 - q - q^2 - q^4 - q^6 + q^7 - q^8 - q^10 + q^11 - 2q^12 - …`,
`b_1(1/5) = -1.2416538502159946385…`. -/
noncomputable def ch10b1 (q : ℂ) : ℂ :=
  -(qPochInf (q ^ 5) (q ^ 5) * qPochInf (q ^ 10) (q ^ 10) * ramanujanTheta (-(q ^ 2)) (-(q ^ 3))) /
    (ramanujanTheta (-(q ^ 2)) (-(q ^ 8)) * ramanujanTheta (-q) (-(q ^ 4)))

end RamanujanLostNotebook.PartV


