-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch08_ch08P
-- name    : RamanujanLostNotebook_PartII_ch08_ch08P
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:55:30.956515+00:00
-- url     : https://prove2.me/theorems/852b093d-5ee2-40d6-9241-0ace7a1dd846
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 8: ch08P
-- statement:
--   Product expression for p from (8.3.2). Its equality to uvw is asserted separately.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 8.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_thetaChi

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Product expression for p from (8.3.2). Its equality to uvw is asserted separately. -/
def ch08P (q : ℂ) : ℂ :=
  8 * q ^ 2 * thetaChi q / thetaChi (q ^ 7) ^ 7

end RamanujanLostNotebook.PartII

end


