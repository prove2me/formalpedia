-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM5
-- name    : RamanujanLostNotebook_PartV_ch05_mtcM5
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:58:47.174998+00:00
-- url     : https://prove2.me/theorems/d4fd75c9-6a2b-4717-9de2-77d6ecb148c4
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 5: mtcM5
-- statement:
--   `M_5(q) = f_0(q) + 2Φ(q^2) - φ(-q^5) G(q)` ((5.1.11), p. 60), with `f_0` of (3.1.1) and `φ` the
--   theta function of (2.3.1).  Domain: `‖q‖ < 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF0
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrG
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPhi

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `M_5(q) = f_0(q) + 2Φ(q^2) - φ(-q^5) G(q)` ((5.1.11), p. 60), with `f_0` of (3.1.1) and `φ` the
theta function of (2.3.1).  Domain: `‖q‖ < 1`. -/
def mtcM5 (q : ℂ) : ℂ :=
  mockF0 q + 2 * mtcPhi (q ^ 2) - thetaPhi (-(q ^ 5)) * rrG q

end RamanujanLostNotebook.PartV

end


