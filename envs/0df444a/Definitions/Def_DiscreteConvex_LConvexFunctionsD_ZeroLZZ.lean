-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
-- name    : DiscreteConvex_LConvexFunctionsD_ZeroLZZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:06:51.538797+00:00
-- url     : https://prove2.me/theorems/3efc1194-efd4-4178-a005-5ea13d2d4254
-- title:
--   ZeroLZZ
-- statement:
--   The class $0L[\mathbb Z\to\mathbb Z]$: integer-valued members of $0L[\mathbb Z\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValuedFn

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[Z→Z]`: integer-valued members of `0L[Z→R]`. -/
def ZeroLZZ (g : (V → ℤ) → WithTop ℝ) : Prop := ZeroLZ g ∧ IsIntegerValuedFn g

end DiscreteConvex.LConvexFunctionsD


