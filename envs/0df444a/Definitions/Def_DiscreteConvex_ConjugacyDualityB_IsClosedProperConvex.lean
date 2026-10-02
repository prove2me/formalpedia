-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsClosedProperConvex
-- name    : DiscreteConvex_ConjugacyDualityB_IsClosedProperConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:32:53.368777+00:00
-- url     : https://prove2.me/theorems/09434844-b1e5-4461-a66f-7a222bc97e5e
-- title:
--   IsClosedProperConvex
-- statement:
--   $f$ is a closed proper convex function on $\mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, supporting Theorem 8.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210, supporting Theorem 8.6

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsConvexWithTop

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is a closed proper convex function on `Rⱽ`. -/
def IsClosedProperConvex (f : (V → ℝ) → WithTop ℝ) : Prop :=
  (DomR f).Nonempty ∧ LowerSemicontinuous f ∧ IsConvexWithTop f

end DiscreteConvex.ConjugacyDualityB


