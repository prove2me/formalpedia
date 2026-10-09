-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_eulerF
-- name    : RamanujanNotebooks_shared_eulerF
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:21:38.774256+00:00
-- url     : https://prove2.me/theorems/654ed04f-9318-42cd-b014-2200801919ed
-- title:
--   Ramanujan's Notebooks, shared: eulerF
-- statement:
--   Ramanujan's `f(-q) = (q; q)_∞` (Entry 22(iii), Part III, p. 36).  The argument of
--   `eulerF` is `q` itself: `eulerF q` is Berndt's `f(-q)`, his `f(-q^5)` is `eulerF (q ^ 5)`,
--   and his `f(q)` is `eulerF (-q)`.
--
--   Berndt writes `f(-q) := f(-q, -q^2)` and the product `(q; q)_∞` is the assertion of Entry
--   22(iii) (Euler's pentagonal number theorem); here the PRODUCT is the definition, and
--   `ramanujanTheta (-q) (-(q ^ 2)) = eulerF q` is the theorem.
--
--   Domain: `‖q‖ < 1`.  Outside: junk of `qPochInf`.
--   Reference: `1 - q - q^2 + q^5 + q^7 - …`, value at `1/5`: `0.76033279587123242010…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_qPochInf

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `f(-q) = (q; q)_∞` (Entry 22(iii), Part III, p. 36).  The argument of
`eulerF` is `q` itself: `eulerF q` is Berndt's `f(-q)`, his `f(-q^5)` is `eulerF (q ^ 5)`,
and his `f(q)` is `eulerF (-q)`.

Berndt writes `f(-q) := f(-q, -q^2)` and the product `(q; q)_∞` is the assertion of Entry
22(iii) (Euler's pentagonal number theorem); here the PRODUCT is the definition, and
`ramanujanTheta (-q) (-(q ^ 2)) = eulerF q` is the theorem.

Domain: `‖q‖ < 1`.  Outside: junk of `qPochInf`.
Reference: `1 - q - q^2 + q^5 + q^7 - …`, value at `1/5`: `0.76033279587123242010…`. -/
def eulerF (q : ℂ) : ℂ :=
  qPochInf q q

end RamanujanNotebooks

end


