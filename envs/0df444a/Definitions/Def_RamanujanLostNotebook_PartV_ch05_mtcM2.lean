-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM2
-- name    : RamanujanLostNotebook_PartV_ch05_mtcM2
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:59:14.293797+00:00
-- url     : https://prove2.me/theorems/769160aa-8d6b-486d-8e42-2061fe5858b1
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 5: mtcM2
-- statement:
--   `M_2(q) = F_0(q) - 1 - Φ(q) + q ψ(q^5) H(q^2)` ((5.1.8), p. 60), with `F_0` of (3.1.4), `ψ` of
--   (2.3.6) and `H` the series (3.1.17).  Domain: `‖q‖ < 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockBigF0
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrH
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPsi

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `M_2(q) = F_0(q) - 1 - Φ(q) + q ψ(q^5) H(q^2)` ((5.1.8), p. 60), with `F_0` of (3.1.4), `ψ` of
(2.3.6) and `H` the series (3.1.17).  Domain: `‖q‖ < 1`. -/
def mtcM2 (q : ℂ) : ℂ :=
  mockBigF0 q - 1 - mtcPhi q + q * thetaPsi (q ^ 5) * rrH (q ^ 2)

end RamanujanLostNotebook.PartV

end


