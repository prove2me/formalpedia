-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rrH
-- name    : RamanujanLostNotebook_PartV_shared_rrH
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:21.020264+00:00
-- url     : https://prove2.me/theorems/636afbfe-8c2f-49f2-88a9-203966243b98
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rrH
-- statement:
--   Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the SERIES in
--   (3.1.17), p. 19.  Domain: `‖q‖ < 1`; equals `rrHProd q` there by the second
--   Rogers–Ramanujan identity.
--   Reference: `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + …`, `H(1/5) = 1.0500833387096912048…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the SERIES in
(3.1.17), p. 19.  Domain: `‖q‖ < 1`; equals `rrHProd q` there by the second
Rogers–Ramanujan identity.
Reference: `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + …`, `H(1/5) = 1.0500833387096912048…`. -/
def rrH (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2 + n) / qPoch q q n

end RamanujanLostNotebook.PartV

end


