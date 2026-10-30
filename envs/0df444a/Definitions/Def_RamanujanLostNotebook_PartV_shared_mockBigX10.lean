-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockBigX10
-- name    : RamanujanLostNotebook_PartV_shared_mockBigX10
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:09:54.577071+00:00
-- url     : https://prove2.me/theorems/415bea81-2579-4f41-a1b1-4c5c97ad69f5
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockBigX10
-- statement:
--   `X_10(q) = ∑_{n ≥ 0} (-1)^n q^{n^2} / (-q; q)_{2n}` ((8.1.3), p. 149; capital chi).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 - q + q^2 + q^4 - 2q^5 + q^6 - q^7 + q^8 - 2q^9 + 3q^10 - …`,
--   `X_10(1/5) = 0.84101302807517249902…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `X_10(q) = ∑_{n ≥ 0} (-1)^n q^{n^2} / (-q; q)_{2n}` ((8.1.3), p. 149; capital chi).
Domain: `‖q‖ < 1`.
Reference: `1 - q + q^2 + q^4 - 2q^5 + q^6 - q^7 + q^8 - 2q^9 + 3q^10 - …`,
`X_10(1/5) = 0.84101302807517249902…`. -/
def mockBigX10 (q : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * q ^ (n ^ 2) / qPoch (-q) q (2 * n)

end RamanujanLostNotebook.PartV

end


