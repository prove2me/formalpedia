-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IntegralPolyhedralFunction
-- name    : DiscreteConvex_MConvexFunctionsE_IntegralPolyhedralFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:44.756757+00:00
-- url     : https://prove2.me/theorems/2280a1ce-8413-4cc8-bed4-e4b44ae25538
-- title:
--   IntegralPolyhedralFunction
-- statement:
--   $f$ has arg-min-integrality: $\arg\min f[-p]$ is an integral polyhedron for every weight $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Eq. (6.75).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Eq. (6.75)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsIntegralPolyhedron

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` has arg-min-integrality: `arg min f[-p]` is an integral polyhedron for every weight `p`. -/
def IntegralPolyhedralFunction (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f p)).Nonempty →
    IsIntegralPolyhedron (ArgMinOn (LinearWeightR f p))

end DiscreteConvex.MConvexFunctionsE


