-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM4
-- name    : RamanujanLostNotebook_PartV_ch05_mtcM4
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:58:46.557123+00:00
-- url     : https://prove2.me/theorems/0c1d8bdf-eb3a-4e88-b1f4-c80dbd5c376f
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 5: mtcM4
-- statement:
--   `M_4(q) = ψ_0(q) - Φ(q^2) - q H(q) f(-q^9, -q)` ((5.1.10), p. 60), with `ψ_0` of (3.1.3) and
--   `f(a, b)` Ramanujan's theta function (5.1.1).  Domain: `‖q‖ < 1`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi0
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_ramanujanTheta
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrH

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `M_4(q) = ψ_0(q) - Φ(q^2) - q H(q) f(-q^9, -q)` ((5.1.10), p. 60), with `ψ_0` of (3.1.3) and
`f(a, b)` Ramanujan's theta function (5.1.1).  Domain: `‖q‖ < 1`. -/
def mtcM4 (q : ℂ) : ℂ :=
  mockPsi0 q - mtcPhi (q ^ 2) - q * rrH q * ramanujanTheta (-(q ^ 9)) (-q)

end RamanujanLostNotebook.PartV

end


