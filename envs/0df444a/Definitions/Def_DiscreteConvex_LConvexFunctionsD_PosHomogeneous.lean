-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous
-- name    : DiscreteConvex_LConvexFunctionsD_PosHomogeneous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:11.240537+00:00
-- url     : https://prove2.me/theorems/938c5c2b-c021-4a1b-9ceb-e403db522c3c
-- title:
--   PosHomogeneous
-- statement:
--   $g$ is positively homogeneous.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (3.32)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is positively homogeneous. -/
def PosHomogeneous (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ t : ℝ, 0 < t → g (fun v => t * x v) = PosScalarMul t (g x)

end DiscreteConvex.LConvexFunctionsD


