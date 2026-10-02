-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVecOptR
-- name    : DiscreteConvex_MConvexFunctionsD_CharVecOptR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:42.174453+00:00
-- url     : https://prove2.me/theorems/b03562a3-e6a2-4800-9f47-7af4fa818302
-- title:
--   CharVecOptR
-- statement:
--   The real-valued characteristic vector of an element of $V\cup\{0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVecOptR (u : Option V) : V → ℝ := u.elim (fun _ => 0) (fun u v => CharVec u v)

end DiscreteConvex.MConvexFunctionsD


