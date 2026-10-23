-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch04_ch04C
-- name    : RamanujanLostNotebook_PartI_ch04_ch04C
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:55:44.539009+00:00
-- url     : https://prove2.me/theorems/1a480e1b-3838-499e-815b-258be7f5e46d
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 4: ch04C
-- statement:
--   The normalized reciprocal Rogers–Ramanujan fraction C(q), (4.1.2)–(4.1.3),
--   printed p.107. This product removes the fifth-root factor before taking the reciprocal.
--   On ‖q‖<1 its four product factors are nonzero; at q=0 it is the analytic value 1.
--   It equals G(q)/H(q) by the Rogers–Ramanujan identities; that equality is not a definition.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 4.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The normalized reciprocal Rogers–Ramanujan fraction C(q), (4.1.2)–(4.1.3),
printed p.107. This product removes the fifth-root factor before taking the reciprocal.
On ‖q‖<1 its four product factors are nonzero; at q=0 it is the analytic value 1.
It equals G(q)/H(q) by the Rogers–Ramanujan identities; that equality is not a definition. -/
def ch04C (q : ℂ) : ℂ :=
  qPochInf (q ^ 2) (q ^ 5) * qPochInf (q ^ 3) (q ^ 5) /
    (qPochInf q (q ^ 5) * qPochInf (q ^ 4) (q ^ 5))

end RamanujanLostNotebook.PartI

end


