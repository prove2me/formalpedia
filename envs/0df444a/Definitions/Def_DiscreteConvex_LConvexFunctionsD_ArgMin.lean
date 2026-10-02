-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMin
-- name    : DiscreteConvex_LConvexFunctionsD_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:58:56.194161+00:00
-- url     : https://prove2.me/theorems/b44475d2-e68c-454b-b399-8cc88c330bb5
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.LConvexFunctionsD


