-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi10
-- name    : RamanujanLostNotebook_PartV_shared_mockPsi10
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:01.488987+00:00
-- url     : https://prove2.me/theorems/98ca16b5-540c-4c01-8fa6-db2948e4fb74
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPsi10
-- statement:
--   `ψ_10(q) = ∑_{n ≥ 1} q^{n(n+1)/2} / (q; q^2)_n
--              = ∑_{m ≥ 0} q^{(m+1)(m+2)/2} / (q; q^2)_{m+1}` ((8.1.2), p. 149; (12.1.1)).
--   Domain: `‖q‖ < 1`.
--   Reference: `q + q^2 + 2q^3 + 2q^4 + 2q^5 + 4q^6 + 4q^7 + 4q^8 + 6q^9 + …`,
--   `ψ_10(1/5) = 0.26016144525381346602…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `ψ_10(q) = ∑_{n ≥ 1} q^{n(n+1)/2} / (q; q^2)_n
           = ∑_{m ≥ 0} q^{(m+1)(m+2)/2} / (q; q^2)_{m+1}` ((8.1.2), p. 149; (12.1.1)).
Domain: `‖q‖ < 1`.
Reference: `q + q^2 + 2q^3 + 2q^4 + 2q^5 + 4q^6 + 4q^7 + 4q^8 + 6q^9 + …`,
`ψ_10(1/5) = 0.26016144525381346602…`. -/
def mockPsi10 (q : ℂ) : ℂ :=
  ∑' m : ℕ, q ^ ((m + 1) * (m + 2) / 2) / qPoch q (q ^ 2) (m + 1)

end RamanujanLostNotebook.PartV

end


