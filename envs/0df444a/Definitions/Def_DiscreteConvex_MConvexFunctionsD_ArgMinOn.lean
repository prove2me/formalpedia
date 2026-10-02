-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ArgMinOn
-- name    : DiscreteConvex_MConvexFunctionsD_ArgMinOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:10.926346+00:00
-- url     : https://prove2.me/theorems/6a16a909-455e-4867-abdb-e8b7f5e80bb9
-- title:
--   ArgMinOn
-- statement:
--   The minimizer set of a `WithTop ℝ`-valued function on any domain type.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, generalized.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, generalized

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def ArgMinOn {W : Type*} (g : W → WithTop ℝ) : Set W := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.MConvexFunctionsD


