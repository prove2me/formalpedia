-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rrHProd
-- name    : RamanujanLostNotebook_PartV_shared_rrHProd
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:25.244626+00:00
-- url     : https://prove2.me/theorems/5d08b5de-762b-4061-8cff-a133ed8355fc
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rrHProd
-- statement:
--   `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)`, the PRODUCT form of `H(q)` ((3.1.17); definition of
--   `H` in (9.2.4), p. 186, and (19.2.2), p. 390).  Domain: `‖q‖ < 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)`, the PRODUCT form of `H(q)` ((3.1.17); definition of
`H` in (9.2.4), p. 186, and (19.2.2), p. 390).  Domain: `‖q‖ < 1`. -/
def rrHProd (q : ℂ) : ℂ :=
  1 / (qPochInf (q ^ 2) (q ^ 5) * qPochInf (q ^ 3) (q ^ 5))

end RamanujanLostNotebook.PartV

end


