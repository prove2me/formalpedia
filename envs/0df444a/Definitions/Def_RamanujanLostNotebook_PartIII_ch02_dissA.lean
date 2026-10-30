-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissA
-- name    : RamanujanLostNotebook_PartIII_ch02_dissA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:17:09.789796+00:00
-- url     : https://prove2.me/theorems/9c91139a-f01e-4c19-8c2f-dfdf515318de
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 2: dissA
-- statement:
--   `A(q) = (q^5; q^5)_∞ G^2(q) / H(q)` ((2.1.7), p. 10), with the PRODUCTS `G`, `H` of
--   (2.1.11)–(2.1.12).  Domain `‖q‖ < 1`; `dissA 0 = 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrGProd
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrHProd

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `A(q) = (q^5; q^5)_∞ G^2(q) / H(q)` ((2.1.7), p. 10), with the PRODUCTS `G`, `H` of
(2.1.11)–(2.1.12).  Domain `‖q‖ < 1`; `dissA 0 = 1`. -/
def dissA (q : ℂ) : ℂ :=
  qPochInf (q ^ 5) (q ^ 5) * rrGProd q ^ 2 / rrHProd q

end RamanujanLostNotebook.PartIII

end


