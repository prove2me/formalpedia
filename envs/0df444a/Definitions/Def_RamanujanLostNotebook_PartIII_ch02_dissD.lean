-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissD
-- name    : RamanujanLostNotebook_PartIII_ch02_dissD
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:18:41.836702+00:00
-- url     : https://prove2.me/theorems/fe8eec33-d5c1-47d9-9dff-c5cab3a7993a
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 2: dissD
-- statement:
--   `D(q) = (q^5; q^5)_∞ H^2(q) / G(q)` ((2.1.10), p. 10).  Domain `‖q‖ < 1`; `dissD 0 = 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrGProd
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrHProd

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `D(q) = (q^5; q^5)_∞ H^2(q) / G(q)` ((2.1.10), p. 10).  Domain `‖q‖ < 1`; `dissD 0 = 1`. -/
def dissD (q : ℂ) : ℂ :=
  qPochInf (q ^ 5) (q ^ 5) * rrHProd q ^ 2 / rrGProd q

end RamanujanLostNotebook.PartIII

end


