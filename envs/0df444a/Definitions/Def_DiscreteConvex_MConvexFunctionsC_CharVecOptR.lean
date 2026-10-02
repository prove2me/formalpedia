-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVecOptR
-- name    : DiscreteConvex_MConvexFunctionsC_CharVecOptR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:54.510997+00:00
-- url     : https://prove2.me/theorems/fb3b633a-2d2f-491c-bbba-d7948540ac85
-- title:
--   CharVecOptR
-- statement:
--   The real-valued characteristic vector of an element of $V\cup\{0\}$, with $\chi_0=0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVecOptR (u : Option V) : V → ℝ := u.elim (fun _ => 0) (fun u v => CharVec u v)

end DiscreteConvex.MConvexFunctionsC


