-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsConvexWithTop
-- name    : DiscreteConvex_ConjugacyDualityB_IsConvexWithTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:53.920144+00:00
-- url     : https://prove2.me/theorems/6e9d016b-ee9a-4241-be29-987dc6d2fda5
-- title:
--   IsConvexWithTop
-- statement:
--   $f$ is convex: for every $x,y$ and $t\in[0,1]$, $f(tx+(1-t)y)\le t\bullet f(x)+(1-t)\bullet f(y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_PosScalarMul

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is convex: for every `x,y` and `t ∈ [0,1]`, `f(tx+(1-t)y) ≤ t•f(x)+(1-t)•f(y)`. -/
def IsConvexWithTop (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (fun v => t * x v + (1 - t) * y v) ≤ PosScalarMul t (f x) + PosScalarMul (1 - t) (f y)

end DiscreteConvex.ConjugacyDualityB


