-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF
-- name    : RamanujanLostNotebook_PartII_shared_eulerF
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:19:53.057715+00:00
-- url     : https://prove2.me/theorems/d76f90d8-546a-4f6a-9d55-eb7cc825ac78
-- title:
--   Ramanujan's Lost Notebook Part II, shared: eulerF
-- statement:
--   Ramanujan's `f(-q) = (q; q)_∞`.  In (1.4.11), p. 17, and (8.1.4), p. 174, it is introduced
--   as `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`, which equals `(q; q)_∞` by Euler's
--   pentagonal number theorem; (3.1.3), p. 53, sets it equal to `(q; q)_∞` directly.  The
--   definition here is the product; the series form is the pentagonal number theorem, a theorem
--   about it.
--
--   Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
--   `eulerF (q ^ 5)`, and the book's one-argument `f(q)` is `eulerF (-q) = (-q; -q)_∞`, which is
--   the two-argument `f(q, -q^2)`.
--   Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
--   Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
--   `eulerF (1/5) = 0.76033279587123242010…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ramanujan's `f(-q) = (q; q)_∞`.  In (1.4.11), p. 17, and (8.1.4), p. 174, it is introduced
as `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`, which equals `(q; q)_∞` by Euler's
pentagonal number theorem; (3.1.3), p. 53, sets it equal to `(q; q)_∞` directly.  The
definition here is the product; the series form is the pentagonal number theorem, a theorem
about it.

Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
`eulerF (q ^ 5)`, and the book's one-argument `f(q)` is `eulerF (-q) = (-q; -q)_∞`, which is
the two-argument `f(q, -q^2)`.
Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
`eulerF (1/5) = 0.76033279587123242010…`. -/
def eulerF (q : ℂ) : ℂ :=
  qPochInf q q

end RamanujanLostNotebook.PartII

end


