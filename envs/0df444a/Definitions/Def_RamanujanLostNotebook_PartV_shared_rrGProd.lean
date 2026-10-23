-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rrGProd
-- name    : RamanujanLostNotebook_PartV_shared_rrGProd
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:06:16.927975+00:00
-- url     : https://prove2.me/theorems/37d8c550-5181-471c-8a5d-7e34f0309bc4
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rrGProd
-- statement:
--   `1 / ((q; q^5)_∞ (q^4; q^5)_∞)`, the PRODUCT form of `G(q)` ((3.1.16); it is the
--   definition of `G` in (9.2.3), p. 185, and (19.2.2), p. 390).  Domain: `‖q‖ < 1`, where the
--   denominator is nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `1 / ((q; q^5)_∞ (q^4; q^5)_∞)`, the PRODUCT form of `G(q)` ((3.1.16); it is the
definition of `G` in (9.2.3), p. 185, and (19.2.2), p. 390).  Domain: `‖q‖ < 1`, where the
denominator is nonzero. -/
def rrGProd (q : ℂ) : ℂ :=
  1 / (qPochInf q (q ^ 5) * qPochInf (q ^ 4) (q ^ 5))

end RamanujanLostNotebook.PartV

end


