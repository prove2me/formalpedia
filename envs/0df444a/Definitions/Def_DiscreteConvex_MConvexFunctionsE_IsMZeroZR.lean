-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroZR
-- name    : DiscreteConvex_MConvexFunctionsE_IsMZeroZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:09:49.130974+00:00
-- url     : https://prove2.me/theorems/830858c5-a7c7-4f17-9c1f-0eebb1d34f44
-- title:
--   IsMZeroZR
-- statement:
--   The class $M_0[\mathbb Z|\mathbb R]$: integral members of $M_0[\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.168, class $M_0[\\mathbb Z|\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.168, class $M_0[\\mathbb Z|\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `M0[Z|R]`: integral members of `M0[R]`. -/
def IsMZeroZR (P : Set (V → ℝ)) : Prop := IsMZeroR P ∧ IsIntegralPolyhedron P

end DiscreteConvex.MConvexFunctionsE


