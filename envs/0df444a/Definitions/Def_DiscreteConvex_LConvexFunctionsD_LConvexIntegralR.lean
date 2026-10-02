-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
-- name    : DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:04:13.020993+00:00
-- url     : https://prove2.me/theorems/73379968-a212-4327-8404-655961ce0b6a
-- title:
--   LConvexIntegralR
-- statement:
--   The class $L[\mathbb Z|\mathbb R\to\mathbb R]$: polyhedral L-convex functions with arg-min-integrality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.198, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.198, class $L[\\mathbb Z|\\mathbb R\\to\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IntegralPolyhedralFunctionR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `L[Z|R→R]`: polyhedral L-convex functions with arg-min-integrality. -/
def LConvexIntegralR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  SBFR g ∧ TRFR g ∧ IntegralPolyhedralFunctionR g

end DiscreteConvex.LConvexFunctionsD


