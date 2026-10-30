-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM3
-- name    : RamanujanLostNotebook_PartV_ch05_mtcM3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:58:31.679989+00:00
-- url     : https://prove2.me/theorems/40823e17-5c72-4f38-8f9c-2d6120cdc901
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 5: mtcM3
-- statement:
--   `M_3(q) = φ_0(-q) + Φ(q) - (q^5; q^5)_∞ G(q^2) H(q) / H(q^2)` ((5.1.9), p. 60), with `φ_0` of
--   (3.1.2) and `G`, `H` the series (3.1.16), (3.1.17).  Domain: `‖q‖ < 1`.
--   There `H(q^2) ≠ 0` (second Rogers–Ramanujan identity), so the quotient is a true quotient.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi0
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrG
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrH

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `M_3(q) = φ_0(-q) + Φ(q) - (q^5; q^5)_∞ G(q^2) H(q) / H(q^2)` ((5.1.9), p. 60), with `φ_0` of
(3.1.2) and `G`, `H` the series (3.1.16), (3.1.17).  Domain: `‖q‖ < 1`.
There `H(q^2) ≠ 0` (second Rogers–Ramanujan identity), so the quotient is a true quotient. -/
def mtcM3 (q : ℂ) : ℂ :=
  mockPhi0 (-q) + mtcPhi q - qPochInf (q ^ 5) (q ^ 5) * rrG (q ^ 2) * rrH q / rrH (q ^ 2)

end RamanujanLostNotebook.PartV

end


