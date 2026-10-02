-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF
-- name    : DiscreteConvex_MConvexFunctionsE_DeltaF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:57.996308+00:00
-- url     : https://prove2.me/theorems/f2f038cb-4d43-4d99-89d9-f406609634f5
-- title:
--   DeltaF
-- statement:
--   The directional difference $\Delta f(z;v,u) = f(z+\chi_v-\chi_u)-f(z)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.132, directional-difference notation.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.132, directional-difference notation

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional difference `Δf(z; v, u) = f(z + χ_v - χ_u) - f(z)`, Eq. (6.1) notation. -/
noncomputable def DeltaF (f : (V → ℤ) → WithTop ℝ) (z : V → ℤ) (v u : V) : WithTop ℝ :=
  f (fun w => z w + CharVec v w - CharVec u w) - f z

end DiscreteConvex.MConvexFunctionsE


