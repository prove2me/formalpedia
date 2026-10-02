-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsMConvexCone
-- name    : DiscreteConvex_ConjugacyDualityB_IsMConvexCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:15.86098+00:00
-- url     : https://prove2.me/theorems/51afd003-834b-4a02-bccf-7490b7d503eb
-- title:
--   IsMConvexCone
-- statement:
--   $C$ is an M-convex cone.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.210

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MConvexPolyhedron
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsCone

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `C` is an M-convex cone. -/
def IsMConvexCone (C : Set (V → ℝ)) : Prop := IsCone C ∧ MConvexPolyhedron C

end DiscreteConvex.ConjugacyDualityB


