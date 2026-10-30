-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_rrH
-- name    : RamanujanLostNotebook_PartI_shared_rrH
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:14:53.807694+00:00
-- url     : https://prove2.me/theorems/3e0d1ac0-fa85-498f-87f8-44682deb607c
-- title:
--   Ramanujan's Lost Notebook Part I, shared: rrH
-- statement:
--   Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the series by which
--   Part I defines `H` in (3.1.3), p. 86 (printed with exponent `n(n+1)`), (4.3.4), p. 114, and
--   (11.1.2), p. 251.  The product `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)` printed beside it is the
--   second Rogers–Ramanujan identity, a theorem about this definition.
--
--   Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
--   Totalization: as for `rrG` (`0` for a term with a vanishing denominator, `0` for
--   `‖q‖ > 1`).
--   Name clash: the `H(q)` of (15.6.25), p. 348, is an unrelated function.
--   Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
--   `rrH (1/5) = 1.0500833387096912048…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Rogers–Ramanujan function `H(q) = ∑_{n ≥ 0} q^{n^2+n} / (q; q)_n`, the series by which
Part I defines `H` in (3.1.3), p. 86 (printed with exponent `n(n+1)`), (4.3.4), p. 114, and
(11.1.2), p. 251.  The product `1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)` printed beside it is the
second Rogers–Ramanujan identity, a theorem about this definition.

Domain: `‖q‖ < 1`, where no `(q; q)_n` vanishes and the series converges absolutely.
Totalization: as for `rrG` (`0` for a term with a vanishing denominator, `0` for
`‖q‖ > 1`).
Name clash: the `H(q)` of (15.6.25), p. 348, is an unrelated function.
Reference: Taylor expansion `1 + q^2 + q^3 + q^4 + q^5 + 2q^6 + 2q^7 + 3q^8 + 3q^9 + …`;
`rrH (1/5) = 1.0500833387096912048…`. -/
def rrH (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2 + n) / qPoch q q n

end RamanujanLostNotebook.PartI

end


