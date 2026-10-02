-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym
-- name    : DiscreteConvex_MConvexFunctionsE_MinDownSym
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:48.52185+00:00
-- url     : https://prove2.me/theorems/057a24ec-e47d-469c-a119-5ff7e27d3438
-- title:
--   MinDownSym
-- statement:
--   $\min_{u,v}\min\{f(x-\chi_u+\chi_v),f(y+\chi_u-\chi_v)\}$, the common right-hand side of (6.93)/(6.96).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Eq. (6.93) right-hand side.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Eq. (6.93) right-hand side

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `min_{u,v} min{f(x-χ_u+χ_v), f(y+χ_u-χ_v)}`, the common RHS of (6.93)/(6.96). -/
noncomputable def MinDownSym (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : WithTop ℝ :=
  (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
    min (f (fun w => x w - CharVec u w + CharVec v w))
      (f (fun w => y w + CharVec u w - CharVec v w))))

end DiscreteConvex.MConvexFunctionsE


