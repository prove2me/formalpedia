-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IntegralPolyhedralFunction
-- name    : DiscreteConvex_MConvexFunctionsD_IntegralPolyhedralFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:52.304128+00:00
-- url     : https://prove2.me/theorems/45d2544f-e5b7-4b01-b67a-9cbd9539dac7
-- title:
--   IntegralPolyhedralFunction
-- statement:
--   $f$ has arg-min-integrality: $\arg\min f[-p]$ is an integral polyhedron for every weight $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Eq. (6.75).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, Eq. (6.75)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` (a polyhedral convex function) has arg-min-integrality (Eq. (6.75)): `arg min f[-p]` is
an integral polyhedron for every weight `p`. -/
def IntegralPolyhedralFunction (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f p)).Nonempty → IsIntegralPolyhedron (ArgMinOn (LinearWeightR f p))

end DiscreteConvex.MConvexFunctionsD


