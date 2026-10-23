-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF0
-- name    : RamanujanLostNotebook_PartV_shared_mockF0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:09:32.094366+00:00
-- url     : https://prove2.me/theorems/6e805fa8-8a16-44ae-ba0f-57caef84d399
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockF0
-- statement:
--   `f_0(q) = ∑_{n ≥ 0} q^{n^2} / (-q; q)_n` ((3.1.1), p. 17).  Domain: `‖q‖ < 1`.
--   Reference: `1 + q - q^2 + q^3 - q^6 + q^7 + q^9 - 2q^10 + …`,
--   `f_0(1/5) = 1.1679491249543262349…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `f_0(q) = ∑_{n ≥ 0} q^{n^2} / (-q; q)_n` ((3.1.1), p. 17).  Domain: `‖q‖ < 1`.
Reference: `1 + q - q^2 + q^3 - q^6 + q^7 + q^9 - 2q^10 + …`,
`f_0(1/5) = 1.1679491249543262349…`. -/
def mockF0 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / qPoch (-q) q n

end RamanujanLostNotebook.PartV

end


