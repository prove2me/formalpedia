-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch02_dissB
-- name    : RamanujanLostNotebook_PartIII_ch02_dissB
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:16:44.315567+00:00
-- url     : https://prove2.me/theorems/c557d7fb-2c75-479c-a632-b81c2e6c712b
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 2: dissB
-- statement:
--   `B(q) = (q^5; q^5)_∞ G(q)` ((2.1.8), p. 10).  Domain `‖q‖ < 1`; `dissB 0 = 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 2.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrGProd

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- `B(q) = (q^5; q^5)_∞ G(q)` ((2.1.8), p. 10).  Domain `‖q‖ < 1`; `dissB 0 = 1`. -/
def dissB (q : ℂ) : ℂ :=
  qPochInf (q ^ 5) (q ^ 5) * rrGProd q

end RamanujanLostNotebook.PartIII

end


