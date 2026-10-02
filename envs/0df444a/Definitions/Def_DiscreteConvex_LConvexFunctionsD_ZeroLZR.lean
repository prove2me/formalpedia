-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZR
-- name    : DiscreteConvex_LConvexFunctionsD_ZeroLZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:01.493323+00:00
-- url     : https://prove2.me/theorems/d17e7fd1-cd92-4806-ae3c-598a39d995cf
-- title:
--   ZeroLZR
-- statement:
--   The class $0L[\mathbb Z|\mathbb R\to\mathbb R]$: $0L[\mathbb R\to\mathbb R]$ functions with arg-min-integrality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, class $0L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.194, class $0L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntegralPolyhedralFunctionR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[Z|R→R]`: `0L[R→R]` functions with arg-min-integrality. -/
def ZeroLZR (g : (V → ℝ) → WithTop ℝ) : Prop := ZeroLR g ∧ IntegralPolyhedralFunctionR g

end DiscreteConvex.LConvexFunctionsD


