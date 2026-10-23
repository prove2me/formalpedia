-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_rrG
-- name    : RamanujanLostNotebook_PartI_shared_rrG
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:16:15.036291+00:00
-- url     : https://prove2.me/theorems/4dd2eb56-93b3-4f32-89cd-6b3160a969fb
-- title:
--   Ramanujan's Lost Notebook Part I, shared: rrG
-- statement:
--   Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the series by which Part I
--   defines `G` in (3.1.3), p. 86, (4.3.3), p. 114, and (11.1.1), p. 251.  The product
--   `1 / ((q; q^5)_∞ (q^4; q^5)_∞)` printed beside it in (4.3.3) and (11.1.1) is the first
--   Rogers–Ramanujan identity, a theorem about this series definition.
--
--   Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
--   Totalization: a term with `(q; q)_n = 0` (possible only for roots of unity, on `‖q‖ = 1`) is
--   `0` by `x / 0 = 0`; for `‖q‖ > 1` the terms grow, the family is not summable and the value
--   is `0`.
--   Name clash: Part I also writes `G(q)` for the cubic continued fraction ((3.1.6), p. 86) and
--   for an unrelated function in (15.6.5), p. 343; neither is this definition.
--   Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
--   `rrG (1/5) = 1.2520840053849600264…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Rogers–Ramanujan function `G(q) = ∑_{n ≥ 0} q^{n^2} / (q; q)_n`, the series by which Part I
defines `G` in (3.1.3), p. 86, (4.3.3), p. 114, and (11.1.1), p. 251.  The product
`1 / ((q; q^5)_∞ (q^4; q^5)_∞)` printed beside it in (4.3.3) and (11.1.1) is the first
Rogers–Ramanujan identity, a theorem about this series definition.

Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
Totalization: a term with `(q; q)_n = 0` (possible only for roots of unity, on `‖q‖ = 1`) is
`0` by `x / 0 = 0`; for `‖q‖ > 1` the terms grow, the family is not summable and the value
is `0`.
Name clash: Part I also writes `G(q)` for the cubic continued fraction ((3.1.6), p. 86) and
for an unrelated function in (15.6.5), p. 343; neither is this definition.
Reference: Taylor expansion `1 + q + q^2 + q^3 + 2q^4 + 2q^5 + 3q^6 + 3q^7 + 4q^8 + …`;
`rrG (1/5) = 1.2520840053849600264…`. -/
def rrG (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / qPoch q q n

end RamanujanLostNotebook.PartI

end


