-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF3
-- name    : RamanujanLostNotebook_PartV_shared_mockF3
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:09:54.766576+00:00
-- url     : https://prove2.me/theorems/4830e6f7-4a5f-4b77-8ee7-f90885139f80
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mockF3
-- statement:
--   `f_3(q) = ∑_{n ≥ 0} q^{n^2} / (-q; q)_n^2` ((2.1.1), p. 5; Ramanujan's `f(q)`).
--   Domain: `‖q‖ < 1`.
--   Reference: `1 + q - 2q^2 + 3q^3 - 3q^4 + 3q^5 - 5q^6 + 7q^7 - 6q^8 + …`,
--   `f_3(1/5) = 1.1399164971079979314…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `f_3(q) = ∑_{n ≥ 0} q^{n^2} / (-q; q)_n^2` ((2.1.1), p. 5; Ramanujan's `f(q)`).
Domain: `‖q‖ < 1`.
Reference: `1 + q - 2q^2 + 3q^3 - 3q^4 + 3q^5 - 5q^6 + 7q^7 - 6q^8 + …`,
`f_3(1/5) = 1.1399164971079979314…`. -/
def mockF3 (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / (qPoch (-q) q n) ^ 2

end RamanujanLostNotebook.PartV

end


