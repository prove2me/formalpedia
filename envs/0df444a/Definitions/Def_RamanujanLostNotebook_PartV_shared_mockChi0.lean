-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockChi0
-- name    : RamanujanLostNotebook_PartV_shared_mockChi0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:10:20.434793+00:00
-- url     : https://prove2.me/theorems/af2ec17f-5d40-4aa2-86d1-989ddc6ad6e3
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockChi0
-- statement:
--   `χ_0(q) = ∑_{n ≥ 0} q^n / (q^{n+1}; q)_n` ((3.1.5), p. 17).  Domain: `‖q‖ < 1`.
--   Reference: `1 + q + q^2 + 2q^3 + q^4 + 3q^5 + 2q^6 + 3q^7 + 3q^8 + 5q^9 + …`,
--   `χ_0(1/5) = 1.2587370978015414549…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `χ_0(q) = ∑_{n ≥ 0} q^n / (q^{n+1}; q)_n` ((3.1.5), p. 17).  Domain: `‖q‖ < 1`.
Reference: `1 + q + q^2 + 2q^3 + q^4 + 3q^5 + 2q^6 + 3q^7 + 3q^8 + 5q^9 + …`,
`χ_0(1/5) = 1.2587370978015414549…`. -/
def mockChi0 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ n / qPoch (q ^ (n + 1)) q n

end RamanujanLostNotebook.PartV

end


