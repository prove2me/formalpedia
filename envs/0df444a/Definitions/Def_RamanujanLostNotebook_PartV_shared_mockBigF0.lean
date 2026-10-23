-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockBigF0
-- name    : RamanujanLostNotebook_PartV_shared_mockBigF0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:09:21.960563+00:00
-- url     : https://prove2.me/theorems/e17a39ec-7a2e-4dcd-9431-2c149b3eead7
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockBigF0
-- statement:
--   `F_0(q) = ∑_{n ≥ 0} q^{2n^2} / (q; q^2)_n` ((3.1.4), p. 17; capital `F`).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 + q^2 + q^3 + q^4 + q^5 + q^6 + q^7 + 2q^8 + 2q^9 + …`,
--   `F_0(1/5) = 1.0500032258067820412…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `F_0(q) = ∑_{n ≥ 0} q^{2n^2} / (q; q^2)_n` ((3.1.4), p. 17; capital `F`).
Domain: `‖q‖ < 1`.
Reference: `1 + q^2 + q^3 + q^4 + q^5 + q^6 + q^7 + 2q^8 + 2q^9 + …`,
`F_0(1/5) = 1.0500032258067820412…`. -/
def mockBigF0 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (2 * n ^ 2) / qPoch q (q ^ 2) n

end RamanujanLostNotebook.PartV

end


