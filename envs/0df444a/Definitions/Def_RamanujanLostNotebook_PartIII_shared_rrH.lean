-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_rrH
-- name    : RamanujanLostNotebook_PartIII_shared_rrH
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:23:58.996986+00:00
-- url     : https://prove2.me/theorems/712562d3-1b94-4a80-b76b-1ced32ae31d0
-- title:
--   Ramanujan's Lost Notebook Part III, shared: rrH
-- statement:
--   Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the SERIES by which
--   Chapter 8 defines `H` ((8.1.1), p. 217, printed with exponent `n(n+1)`).  Its equality with
--   the product `rrHProd q` is the second Rogers–Ramanujan identity ((8.1.2), p. 217), a theorem
--   about the two definitions.
--
--   Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
--   Totalization: as for `rrG` (`0` for a term with a vanishing denominator, `0` for
--   `‖q‖ > 1`).
--   Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
--   `rrH (1/5) = 1.0500833387096912048…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the SERIES by which
Chapter 8 defines `H` ((8.1.1), p. 217, printed with exponent `n(n+1)`).  Its equality with
the product `rrHProd q` is the second Rogers–Ramanujan identity ((8.1.2), p. 217), a theorem
about the two definitions.

Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
Totalization: as for `rrG` (`0` for a term with a vanishing denominator, `0` for
`‖q‖ > 1`).
Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
`rrH (1/5) = 1.0500833387096912048…`. -/
def rrH (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2 + n) / qPoch q q n

end RamanujanLostNotebook.PartIII

end


