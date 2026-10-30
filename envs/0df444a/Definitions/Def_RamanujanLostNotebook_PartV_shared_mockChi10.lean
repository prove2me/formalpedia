-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockChi10
-- name    : RamanujanLostNotebook_PartV_shared_mockChi10
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:09:39.606682+00:00
-- url     : https://prove2.me/theorems/f2c5f878-83ff-459c-b2ac-1422a0ce2db2
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockChi10
-- statement:
--   `χ_10(q) = ∑_{n ≥ 1} (-1)^{n-1} q^{n^2} / (-q; q)_{2n-1}
--              = ∑_{m ≥ 0} (-1)^m q^{(m+1)^2} / (-q; q)_{2m+1}` ((8.1.4), p. 149; (12.1.2)).
--   Domain: `‖q‖ < 1`.
--   Reference: `q - q^2 + q^3 - 2q^4 + 2q^5 - q^6 + 2q^7 - 3q^8 + 3q^9 - …`,
--   `χ_10(1/5) = 0.16539519660984730135…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `χ_10(q) = ∑_{n ≥ 1} (-1)^{n-1} q^{n^2} / (-q; q)_{2n-1}
           = ∑_{m ≥ 0} (-1)^m q^{(m+1)^2} / (-q; q)_{2m+1}` ((8.1.4), p. 149; (12.1.2)).
Domain: `‖q‖ < 1`.
Reference: `q - q^2 + q^3 - 2q^4 + 2q^5 - q^6 + 2q^7 - 3q^8 + 3q^9 - …`,
`χ_10(1/5) = 0.16539519660984730135…`. -/
def mockChi10 (q : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * q ^ ((m + 1) ^ 2) / qPoch (-q) q (2 * m + 1)

end RamanujanLostNotebook.PartV

end


