-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
-- name    : DiscreteConvex_MConvexFunctionsE_MinDown
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:57.245496+00:00
-- url     : https://prove2.me/theorems/6220ff00-034e-40c1-a1b2-65878bbe399e
-- title:
--   MinDown
-- statement:
--   $\min_{u\in\operatorname{supp}^+(x-y)}\min_{v\in\operatorname{supp}^-(x-y)} f(x-\chi_u+\chi_v)$, the common right-hand side of (6.94)/(6.97).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Eq. (6.94) right-hand side.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Eq. (6.94) right-hand side

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `min_{u ∈ supp+(x-y)} min_{v ∈ supp-(x-y)} f(x - χ_u + χ_v)`, the common RHS of (6.94)/(6.97). -/
noncomputable def MinDown (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : WithTop ℝ :=
  (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
    f (fun w => x w - CharVec u w + CharVec v w)))

end DiscreteConvex.MConvexFunctionsE


