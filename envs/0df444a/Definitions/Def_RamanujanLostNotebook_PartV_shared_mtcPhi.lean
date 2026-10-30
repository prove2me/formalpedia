-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPhi
-- name    : RamanujanLostNotebook_PartV_shared_mtcPhi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:14.513226+00:00
-- url     : https://prove2.me/theorems/f48bebd1-9948-42be-9b02-2d88f6d1a6f7
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mtcPhi
-- statement:
--   `Φ(q) = -1 + ∑_{n ≥ 0} q^{5n^2} / ((q; q^5)_{n+1} (q^4; q^5)_n)` ((5.1.6), p. 60;
--   (19.2.7), p. 391).  Domain: `‖q‖ < 1`.
--   Reference: `q + q^2 + q^3 + q^4 + 2q^5 + 2q^6 + 2q^7 + 2q^8 + 3q^9 + …`,
--   `Φ(1/5) = 0.25040066666832092639…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `Φ(q) = -1 + ∑_{n ≥ 0} q^{5n^2} / ((q; q^5)_{n+1} (q^4; q^5)_n)` ((5.1.6), p. 60;
(19.2.7), p. 391).  Domain: `‖q‖ < 1`.
Reference: `q + q^2 + q^3 + q^4 + 2q^5 + 2q^6 + 2q^7 + 2q^8 + 3q^9 + …`,
`Φ(1/5) = 0.25040066666832092639…`. -/
def mtcPhi (q : ℂ) : ℂ :=
  -1 + ∑' n : ℕ, q ^ (5 * n ^ 2) / (qPoch q (q ^ 5) (n + 1) * qPoch (q ^ 4) (q ^ 5) n)

end RamanujanLostNotebook.PartV

end


