-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi10
-- name    : RamanujanLostNotebook_PartV_shared_mockPhi10
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:59.862684+00:00
-- url     : https://prove2.me/theorems/ee0bd808-217e-4901-9486-c6e4083b4d45
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPhi10
-- statement:
--   `φ_10(q) = ∑_{n ≥ 0} q^{n(n+1)/2} / (q; q^2)_{n+1}` ((8.1.1), p. 149).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 + 2q + 2q^2 + 3q^3 + 4q^4 + 4q^5 + 6q^6 + 7q^7 + 8q^8 + …`,
--   `φ_10(1/5) = 1.5121808021577794337…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `φ_10(q) = ∑_{n ≥ 0} q^{n(n+1)/2} / (q; q^2)_{n+1}` ((8.1.1), p. 149).
Domain: `‖q‖ < 1`.
Reference: `1 + 2q + 2q^2 + 3q^3 + 4q^4 + 4q^5 + 6q^6 + 7q^7 + 8q^8 + …`,
`φ_10(1/5) = 1.5121808021577794337…`. -/
def mockPhi10 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n * (n + 1) / 2) / qPoch q (q ^ 2) (n + 1)

end RamanujanLostNotebook.PartV

end


