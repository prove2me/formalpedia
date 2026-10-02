-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvexFunction
-- name    : DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvexFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:06.725307+00:00
-- url     : https://prove2.me/theorems/e53fa6e4-363b-4160-81de-8ea0149093ad
-- title:
--   IsIntegrallyConvexFunction
-- statement:
--   $f$ is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexClosureValOn
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntegralNeighborhoodFinset

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is integrally convex. -/
def IsIntegrallyConvexFunction (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ConvexClosureVal f p =
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p)) p

end DiscreteConvex.ConjugacyDualityC


