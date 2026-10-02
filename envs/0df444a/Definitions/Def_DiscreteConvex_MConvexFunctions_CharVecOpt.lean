-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_CharVecOpt
-- name    : DiscreteConvex_MConvexFunctions_CharVecOpt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:53:23.094235+00:00
-- url     : https://prove2.me/theorems/45647378-4e77-4f03-a7ba-2f4f6df4d090
-- title:
--   Characteristic vector on the extended index set (chi_0 = 0)
-- statement:
--   The characteristic vector of an element of $V \cup \{0\}$ (represented as `Option V`): $\chi_u$ for $u = \mathrm{some}\ u$, and the zero vector for $u = \mathrm{none}$ (the book's convention $\chi_0 = 0$). Supporting notion for Theorem 6.37's M$^\natural$-case.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, supporting Theorem 6.37.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134 (supporting Theorem 6.37)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134: the characteristic vector convention
`χ₀ = 0` on the extended index set `V ∪ {0}`, used in the M♮-convex case of Theorem 6.37, in
`DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The characteristic vector of an element of `V ∪ \{0\}` (represented as `Option V`, `none`
standing for the new element `0`): `χ_u` for `u = some u`, and the zero vector for `u = none`
(the book's convention `χ₀ = 0`). -/
def CharVecOpt {V : Type*} [DecidableEq V] (u : Option V) : V → ℤ :=
  u.elim (fun _ => 0) CharVec

end DiscreteConvex.MConvexFunctions


