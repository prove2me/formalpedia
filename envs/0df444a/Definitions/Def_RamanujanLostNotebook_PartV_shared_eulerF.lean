-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_eulerF
-- name    : RamanujanLostNotebook_PartV_shared_eulerF
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:09:40.96323+00:00
-- url     : https://prove2.me/theorems/7a23ac25-67df-4e6d-b9bf-4798e7e48d17
-- title:
--   Ramanujan's Lost Notebook Part V, shared: eulerF
-- statement:
--   Ramanujan's `f(-q) = (q; q)_∞` ((6.3.2), p. 85; (15.1.2), p. 322; (16.1.4), p. 357).
--   The argument of `eulerF` is `q` itself: `eulerF q` is the book's `f(-q)`, and the book's
--   `f(-q^5)` is `eulerF (q ^ 5)`.
--
--   Domain: `‖q‖ < 1`.  There it equals `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`
--   (pentagonal number theorem).  Outside: junk of `qPochInf`.
--   Reference: `1 - q - q^2 + q^5 + q^7 - …`, value at `1/5`: `0.76033279587123242010…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Ramanujan's `f(-q) = (q; q)_∞` ((6.3.2), p. 85; (15.1.2), p. 322; (16.1.4), p. 357).
The argument of `eulerF` is `q` itself: `eulerF q` is the book's `f(-q)`, and the book's
`f(-q^5)` is `eulerF (q ^ 5)`.

Domain: `‖q‖ < 1`.  There it equals `f(-q, -q^2) = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2}`
(pentagonal number theorem).  Outside: junk of `qPochInf`.
Reference: `1 - q - q^2 + q^5 + q^7 - …`, value at `1/5`: `0.76033279587123242010…`. -/
def eulerF (q : ℂ) : ℂ :=
  qPochInf q q

end RamanujanLostNotebook.PartV

end


