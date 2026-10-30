-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrG
-- name    : RamanujanLostNotebook_PartIII_shared_rrG
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:24:07.205707+00:00
-- url     : https://prove2.me/theorems/998f1530-a754-4d07-afe2-3324784684bb
-- title:
--   Ramanujan's Lost Notebook Part III, shared: rrG
-- statement:
--   Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the SERIES by which
--   Chapter 8 defines `G` ((8.1.1), p. 217).  Its equality with the product `rrGProd q` is the
--   first Rogers–Ramanujan identity ((8.1.2), p. 217), a theorem about the two definitions.
--
--   Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
--   Totalization: a term with `(q; q)_n = 0` (possible only for roots of unity, on `‖q‖ = 1`) is
--   `0` by `x / 0 = 0`; for `‖q‖ > 1` the terms grow, the family is not summable and the value
--   is `0`.
--   Name clash: the `G(q)` of Section 3.5, p. 59, is an unrelated function.
--   Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
--   `rrG (1/5) = 1.2520840053849600264…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the SERIES by which
Chapter 8 defines `G` ((8.1.1), p. 217).  Its equality with the product `rrGProd q` is the
first Rogers–Ramanujan identity ((8.1.2), p. 217), a theorem about the two definitions.

Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
Totalization: a term with `(q; q)_n = 0` (possible only for roots of unity, on `‖q‖ = 1`) is
`0` by `x / 0 = 0`; for `‖q‖ > 1` the terms grow, the family is not summable and the value
is `0`.
Name clash: the `G(q)` of Section 3.5, p. 59, is an unrelated function.
Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
`rrG (1/5) = 1.2520840053849600264…`. -/
def rrG (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / qPoch q q n

end RamanujanLostNotebook.PartIII

end


