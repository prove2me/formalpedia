-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi6
-- name    : RamanujanLostNotebook_PartV_shared_mockPhi6
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:05:47.577028+00:00
-- url     : https://prove2.me/theorems/3f246919-2122-4b88-8476-6942dc5dff41
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPhi6
-- statement:
--   `φ_6(q) = ∑_{n ≥ 0} (-1)^n (q; q^2)_n q^{n^2} / (-q; q)_{2n}` ((7.1.1), p. 109).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 - q + 2q^2 - q^3 + q^4 - 3q^5 + 3q^6 - 3q^7 + 4q^8 - …`,
--   `φ_6(1/5) = 0.87280229815796834107…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `φ_6(q) = ∑_{n ≥ 0} (-1)^n (q; q^2)_n q^{n^2} / (-q; q)_{2n}` ((7.1.1), p. 109).
Domain: `‖q‖ < 1`.
Reference: `1 - q + 2q^2 - q^3 + q^4 - 3q^5 + 3q^6 - 3q^7 + 4q^8 - …`,
`φ_6(1/5) = 0.87280229815796834107…`. -/
def mockPhi6 (q : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * qPoch q (q ^ 2) n * q ^ (n ^ 2) / qPoch (-q) q (2 * n)

end RamanujanLostNotebook.PartV

end


