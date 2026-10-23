-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockOmega3
-- name    : RamanujanLostNotebook_PartV_shared_mockOmega3
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:05:48.959387+00:00
-- url     : https://prove2.me/theorems/89e9d974-ac69-49b8-b367-408478873bd2
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockOmega3
-- statement:
--   `ω_3(q) = ∑_{n ≥ 0} q^{2n(n+1)} / (q; q^2)_{n+1}^2` ((2.1.5), p. 5).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 + 2q + 3q^2 + 4q^3 + 6q^4 + 8q^5 + 10q^6 + 14q^7 + …`,
--   `ω_3(1/5) = 1.5650404916795025457…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `ω_3(q) = ∑_{n ≥ 0} q^{2n(n+1)} / (q; q^2)_{n+1}^2` ((2.1.5), p. 5).
Domain: `‖q‖ < 1`.
Reference: `1 + 2q + 3q^2 + 4q^3 + 6q^4 + 8q^5 + 10q^6 + 14q^7 + …`,
`ω_3(1/5) = 1.5650404916795025457…`. -/
def mockOmega3 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (2 * n * (n + 1)) / (qPoch q (q ^ 2) (n + 1)) ^ 2

end RamanujanLostNotebook.PartV

end


