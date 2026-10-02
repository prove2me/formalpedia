-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction
-- name    : DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:38:16.873733+00:00
-- url     : https://prove2.me/theorems/7fcc7963-b03e-418b-82eb-af1912a09463
-- title:
--   IsIntegrallyConvexFunction
-- statement:
--   $f$ is **integrally convex**: at every real point, the convex closure agrees with the closure taken using only that point's integral neighborhood.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.100, Eq. (3.71)-(3.72).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.100, Eq. (3.71)-(3.72)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is integrally convex, Eq. (3.71)-adjacent: the convex closure agrees with the local
convex closure taken only over each point's integral neighborhood. -/
def IsIntegrallyConvexFunction (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ConvexClosureVal f p =
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p)) p

end DiscreteConvex.MConvexFunctionsC


