-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM1
-- name    : RamanujanLostNotebook_PartV_ch05_mtcM1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:59:49.81803+00:00
-- url     : https://prove2.me/theorems/f25e10b1-6272-40a4-8978-1c8a2d3338e1
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 5: mtcM1
-- statement:
--   `M_1(q) = χ_0(q) - 2 - 3Φ(q) + A(q)` ((5.1.7), p. 60), with `χ_0` the fifth order mock theta
--   function (3.1.5), `Φ` of (5.1.6) and `A` of (5.1.5).  Domain: `‖q‖ < 1`.
--   The first of the mock theta conjectures is `M_1(q) = 0`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockChi0
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcA
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `M_1(q) = χ_0(q) - 2 - 3Φ(q) + A(q)` ((5.1.7), p. 60), with `χ_0` the fifth order mock theta
function (3.1.5), `Φ` of (5.1.6) and `A` of (5.1.5).  Domain: `‖q‖ < 1`.
The first of the mock theta conjectures is `M_1(q) = 0`. -/
def mtcM1 (q : ℂ) : ℂ :=
  mockChi0 q - 2 - 3 * mtcPhi q + mtcA q

end RamanujanLostNotebook.PartV

end


