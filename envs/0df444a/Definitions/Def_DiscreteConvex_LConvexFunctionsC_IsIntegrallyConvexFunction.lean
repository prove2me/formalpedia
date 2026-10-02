-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction
-- name    : DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:49:33.6436+00:00
-- url     : https://prove2.me/theorems/06c811e7-d0c3-4e01-a361-60db96d57ae9
-- title:
--   IsIntegrallyConvexFunction
-- statement:
--   $g$ is integrally convex: at every real point, the convex closure agrees with the closure taken using only that point's integral neighborhood.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntegralNeighborhoodFinset

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is integrally convex: at every real point, the convex closure agrees with the closure
taken using only that point's integral neighborhood. -/
def IsIntegrallyConvexFunction (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ConvexClosureVal g p =
    ConvexClosureValOn g (Finset.filter (fun y => y ∈ DomZ g) (IntegralNeighborhoodFinset p)) p

end DiscreteConvex.LConvexFunctionsC


