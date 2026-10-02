-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LiftedSetL
-- name    : DiscreteConvex_LConvexFunctionsC_LiftedSetL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:07.594975+00:00
-- url     : https://prove2.me/theorems/08ef1261-5515-4c24-ac6a-688b30d27522
-- title:
--   LiftedSetL
-- statement:
--   The lift of a set $D\subseteq\mathbb Z^V$ to $\mathbb Z^{\tilde V}$ (as `Option V`), mirroring `LiftedFunctionL`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2)-analogue for sets.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Eq. (7.2)-analogue for sets

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a set `D ⊆ Zⱽ` to `Z^Ṽ` (as `Option V`), mirroring `LiftedFunctionL`. -/
def LiftedSetL (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {p : Option V → ℤ | (fun v => p (some v) - p none) ∈ D}

end DiscreteConvex.LConvexFunctionsC


