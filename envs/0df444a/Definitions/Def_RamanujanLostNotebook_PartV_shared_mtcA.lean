-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcA
-- name    : RamanujanLostNotebook_PartV_shared_mtcA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:09:49.993974+00:00
-- url     : https://prove2.me/theorems/a751e481-80d3-4714-a2db-51f8fb295d4b
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mtcA
-- statement:
--   `A(q) = G(q)^2 (q^5; q^5)_∞ / H(q)` ((5.1.5), p. 60; (19.2.3), p. 390), with `G`, `H`
--   the series `rrG`, `rrH` of (3.1.16), (3.1.17).  Domain: `‖q‖ < 1`, where `H(q) ≠ 0`.
--   Reference: `1 + 2q + 2q^2 + q^3 + 2q^4 + 3q^5 + 4q^6 + 3q^7 + …`,
--   `A(1/5) = 1.4924649022034213241…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrG
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rrH

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `A(q) = G(q)^2 (q^5; q^5)_∞ / H(q)` ((5.1.5), p. 60; (19.2.3), p. 390), with `G`, `H`
the series `rrG`, `rrH` of (3.1.16), (3.1.17).  Domain: `‖q‖ < 1`, where `H(q) ≠ 0`.
Reference: `1 + 2q + 2q^2 + q^3 + 2q^4 + 3q^5 + 4q^6 + 3q^7 + …`,
`A(1/5) = 1.4924649022034213241…`. -/
def mtcA (q : ℂ) : ℂ :=
  (rrG q) ^ 2 * qPochInf (q ^ 5) (q ^ 5) / rrH q

end RamanujanLostNotebook.PartV

end


