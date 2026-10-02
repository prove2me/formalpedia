-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn
-- name    : DiscreteConvex_MConvexFunctionsC_ArgMinOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:26.503369+00:00
-- url     : https://prove2.me/theorems/34517257-6211-4205-9403-245e63dc18b9
-- title:
--   ArgMinOn
-- statement:
--   The minimizer set of a `WithTop ℝ`-valued function on any domain type.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148-149, generalized.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148-149, generalized

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a `WithTop ℝ`-valued function on any type. -/
def ArgMinOn {W : Type*} (g : W → WithTop ℝ) : Set W := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.MConvexFunctionsC


