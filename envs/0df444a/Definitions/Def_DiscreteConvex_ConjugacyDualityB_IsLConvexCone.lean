-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsLConvexCone
-- name    : DiscreteConvex_ConjugacyDualityB_IsLConvexCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:25.338134+00:00
-- url     : https://prove2.me/theorems/5c8c3016-41d8-4046-a259-a3cb57d87bc0
-- title:
--   IsLConvexCone
-- statement:
--   $C$ is an L-convex cone.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LConvexPolyhedron
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsCone

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `C` is an L-convex cone. -/
def IsLConvexCone (C : Set (V → ℝ)) : Prop := IsCone C ∧ LConvexPolyhedron C

end DiscreteConvex.ConjugacyDualityB


