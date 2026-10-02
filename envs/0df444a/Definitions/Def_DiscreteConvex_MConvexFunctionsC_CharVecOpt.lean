-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVecOpt
-- name    : DiscreteConvex_MConvexFunctionsC_CharVecOpt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:01.335426+00:00
-- url     : https://prove2.me/theorems/3f189172-3e6f-439f-baa6-9587836860a9
-- title:
--   CharVecOpt
-- statement:
--   The characteristic vector of an element of $V \cup \{0\}$ (`Option V`), with $\chi_0=0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVecOpt (u : Option V) : V → ℤ := u.elim (fun _ => 0) CharVec

end DiscreteConvex.MConvexFunctionsC


