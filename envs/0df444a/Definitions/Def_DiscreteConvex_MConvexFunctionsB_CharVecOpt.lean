-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVecOpt
-- name    : DiscreteConvex_MConvexFunctionsB_CharVecOpt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:07:53.282529+00:00
-- url     : https://prove2.me/theorems/c4ec3794-4ccd-4e6a-8923-e31d10487e14
-- title:
--   CharVecOpt
-- statement:
--   The characteristic vector of an element of $V \cup \{0\}$ (`Option V`, `none`$=0$): $\chi_u$, or the zero vector for the new element $0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134 (supporting Theorem 6.24).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134 (supporting Theorem 6.24)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134 (supporting Theorem 6.24), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The characteristic vector of an element of `V ∪ \{0\}` (`Option V`, `none` = the new
element `0`): `χ_u` for `u = some u`, and the zero vector for `u = none`. -/
def CharVecOpt {V : Type*} [DecidableEq V] (u : Option V) : V → ℤ := u.elim (fun _ => 0) CharVec

end DiscreteConvex.MConvexFunctionsB


