-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvexFunction
-- name    : DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvexFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:08.981997+00:00
-- url     : https://prove2.me/theorems/ae3213b1-00cf-4906-8094-c0d465611d0d
-- title:
--   IsIntegrallyConvexFunction
-- statement:
--   $f$ is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureVal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntegralNeighborhoodFinset

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is integrally convex. -/
def IsIntegrallyConvexFunction (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ConvexClosureVal f p =
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p)) p

end DiscreteConvex.ConjugacyDualityB


