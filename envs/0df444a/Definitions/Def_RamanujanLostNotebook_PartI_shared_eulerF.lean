-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_eulerF
-- name    : RamanujanLostNotebook_PartI_shared_eulerF
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:15:27.620638+00:00
-- url     : https://prove2.me/theorems/841c93d5-379a-4f87-a809-b1d1e4d8b670
-- title:
--   Ramanujan's Lost Notebook Part I, shared: eulerF
-- statement:
--   Ramanujan's `f(-q) = (q; q)_∞`.  In (1.1.8), p. 11, it is introduced as
--   `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`, which equals `(q; q)_∞` by Euler's pentagonal
--   number theorem; (3.1.5), p. 86, and (2.2.2), p. 59, define it directly as `(q; q)_∞`.  The definition here is
--   the product; the series form is the pentagonal number theorem, a theorem about it.
--
--   Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
--   `eulerF (q ^ 5)`, and the book's one-argument `f(q)` is `eulerF (-q) = (-q; -q)_∞`, which is
--   the two-argument `f(q, -q^2)`.
--   Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
--   Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
--   `eulerF (1/5) = 0.76033279587123242010…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Ramanujan's `f(-q) = (q; q)_∞`.  In (1.1.8), p. 11, it is introduced as
`f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`, which equals `(q; q)_∞` by Euler's pentagonal
number theorem; (3.1.5), p. 86, and (2.2.2), p. 59, define it directly as `(q; q)_∞`.  The definition here is
the product; the series form is the pentagonal number theorem, a theorem about it.

Argument convention: `eulerF q` is the book's `f(-q)`.  Hence the book's `f(-q^5)` is
`eulerF (q ^ 5)`, and the book's one-argument `f(q)` is `eulerF (-q) = (-q; -q)_∞`, which is
the two-argument `f(q, -q^2)`.
Domain: `‖q‖ < 1`.  Totalization: that of `qPochInf`; `eulerF 0 = 1`.
Reference: Taylor expansion `1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + …`;
`eulerF (1/5) = 0.76033279587123242010…`. -/
def eulerF (q : ℂ) : ℂ :=
  qPochInf q q

end RamanujanLostNotebook.PartI

end


