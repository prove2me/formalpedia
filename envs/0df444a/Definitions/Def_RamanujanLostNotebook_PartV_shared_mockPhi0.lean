-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi0
-- name    : RamanujanLostNotebook_PartV_shared_mockPhi0
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:56.051022+00:00
-- url     : https://prove2.me/theorems/bf1acb3e-00de-4ff8-b379-58a58455dcd9
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPhi0
-- statement:
--   `φ_0(q) = ∑_{n ≥ 0} (-q; q^2)_n q^{n^2}` ((3.1.2), p. 17).  Domain: `‖q‖ < 1`.
--   Reference: `1 + q + q^2 + q^4 + q^5 + q^7 + q^8 + q^9 + q^10 + …`,
--   `φ_0(1/5) = 1.2419359795213107408…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `φ_0(q) = ∑_{n ≥ 0} (-q; q^2)_n q^{n^2}` ((3.1.2), p. 17).  Domain: `‖q‖ < 1`.
Reference: `1 + q + q^2 + q^4 + q^5 + q^7 + q^8 + q^9 + q^10 + …`,
`φ_0(1/5) = 1.2419359795213107408…`. -/
def mockPhi0 (q : ℂ) : ℂ :=
  ∑' n : ℕ, qPoch (-q) (q ^ 2) n * q ^ (n ^ 2)

end RamanujanLostNotebook.PartV

end


