-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_ArgMin
-- name    : DiscreteConvex_LConvexFunctionsB_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:24.152864+00:00
-- url     : https://prove2.me/theorems/e83f5474-f8f3-44c6-a113-a849551c1ae3
-- title:
--   ArgMin
-- statement:
--   The minimizer set of $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of `g`. -/
def ArgMin (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.LConvexFunctionsB


