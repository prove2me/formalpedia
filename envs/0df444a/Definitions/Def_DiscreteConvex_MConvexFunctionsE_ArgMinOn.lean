-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
-- name    : DiscreteConvex_MConvexFunctionsE_ArgMinOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:31.334272+00:00
-- url     : https://prove2.me/theorems/b8c6fff3-9e4d-4d43-bbb5-07e038a43c31
-- title:
--   ArgMinOn
-- statement:
--   The minimizer set of a `WithTop ℝ`-valued function on any domain type.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, generalized.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, generalized

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a `WithTop ℝ`-valued function on any domain type. -/
def ArgMinOn {W : Type*} (g : W → WithTop ℝ) : Set W := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.MConvexFunctionsE


