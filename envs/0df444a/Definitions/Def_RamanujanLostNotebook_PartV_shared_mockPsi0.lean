-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi0
-- name    : RamanujanLostNotebook_PartV_shared_mockPsi0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:06:13.014094+00:00
-- url     : https://prove2.me/theorems/2974cac4-f442-4c2c-bd84-75b842ab82a5
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPsi0
-- statement:
--   `ψ_0(q) = ∑_{n ≥ 1} (-q; q)_{n-1} q^{n(n+1)/2}` ((3.1.3), p. 17), written with
--   `n = m + 1`.  Domain: `‖q‖ < 1`.
--   Reference: `q + q^3 + q^4 + q^6 + q^7 + q^8 + q^9 + q^10 + q^11 + …`,
--   `ψ_0(1/5) = 0.20968000085885181758…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `ψ_0(q) = ∑_{n ≥ 1} (-q; q)_{n-1} q^{n(n+1)/2}` ((3.1.3), p. 17), written with
`n = m + 1`.  Domain: `‖q‖ < 1`.
Reference: `q + q^3 + q^4 + q^6 + q^7 + q^8 + q^9 + q^10 + q^11 + …`,
`ψ_0(1/5) = 0.20968000085885181758…`. -/
def mockPsi0 (q : ℂ) : ℂ :=
  ∑' m : ℕ, qPoch (-q) q m * q ^ ((m + 1) * (m + 2) / 2)

end RamanujanLostNotebook.PartV

end


