-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi3
-- name    : RamanujanLostNotebook_PartV_shared_mockPhi3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:50.602982+00:00
-- url     : https://prove2.me/theorems/ac307224-222e-4765-9625-c1dcd91bee21
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockPhi3
-- statement:
--   `φ_3(q) = ∑_{n ≥ 0} q^{n^2} / (-q^2; q^2)_n` ((2.1.2), p. 5).  Domain: `‖q‖ < 1`.
--   The function `φ̃(q)` of (4.1.6), p. 36, is this same series.
--   Reference: `1 + q - q^3 + q^4 + q^5 - q^6 - q^7 + 2q^9 - …`,
--   `φ_3(1/5) = 1.1938441877359563776…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `φ_3(q) = ∑_{n ≥ 0} q^{n^2} / (-q^2; q^2)_n` ((2.1.2), p. 5).  Domain: `‖q‖ < 1`.
The function `φ̃(q)` of (4.1.6), p. 36, is this same series.
Reference: `1 + q - q^3 + q^4 + q^5 - q^6 - q^7 + 2q^9 - …`,
`φ_3(1/5) = 1.1938441877359563776…`. -/
def mockPhi3 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / qPoch (-(q ^ 2)) (q ^ 2) n

end RamanujanLostNotebook.PartV

end


