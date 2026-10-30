-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rrG
-- name    : RamanujanLostNotebook_PartV_shared_rrG
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:09.42698+00:00
-- url     : https://prove2.me/theorems/d04ad076-f8eb-4eb2-bf13-d124709cbb7b
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rrG
-- statement:
--   Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the SERIES in
--   (3.1.16), p. 19.  Domain: `‖q‖ < 1`.  By the first Rogers–Ramanujan identity it equals
--   `rrGProd q` there (a theorem, not part of the definition).
--   Reference: `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + …`, `G(1/5) = 1.2520840053849600264…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the SERIES in
(3.1.16), p. 19.  Domain: `‖q‖ < 1`.  By the first Rogers–Ramanujan identity it equals
`rrGProd q` there (a theorem, not part of the definition).
Reference: `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + …`, `G(1/5) = 1.2520840053849600264…`. -/
def rrG (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / qPoch q q n

end RamanujanLostNotebook.PartV

end


