-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissC
-- name    : RamanujanLostNotebook_PartIII_ch02_dissC
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:17:14.825389+00:00
-- url     : https://prove2.me/theorems/8cf42f4e-1183-4cb1-bcad-15affcca700e
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 2: dissC
-- statement:
--   `C(q) = (q^5; q^5)_∞ H(q)` ((2.1.9), p. 10).  Domain `‖q‖ < 1`; `dissC 0 = 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrHProd

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `C(q) = (q^5; q^5)_∞ H(q)` ((2.1.9), p. 10).  Domain `‖q‖ < 1`; `dissC 0 = 1`. -/
def dissC (q : ℂ) : ℂ :=
  qPochInf (q ^ 5) (q ^ 5) * rrHProd q

end RamanujanLostNotebook.PartIII

end


