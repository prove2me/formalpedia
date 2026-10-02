-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MConvexIntegralR
-- name    : DiscreteConvex_MConvexFunctionsE_MConvexIntegralR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:09:12.364191+00:00
-- url     : https://prove2.me/theorems/0dbe1b72-6c2c-4dcb-86e4-5304864ed4a5
-- title:
--   MConvexIntegralR
-- statement:
--   The class $M[\mathbb Z|\mathbb R\to\mathbb R]$: polyhedral M-convex functions with arg-min-integrality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, class $M[\\mathbb Z|\\mathbb R\\to\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, class $M[\\mathbb Z|\\mathbb R\\to\\mathbb R]$

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IntegralPolyhedralFunction

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `M[Z|R→R]`: polyhedral M-convex functions with arg-min-integrality. -/
def MConvexIntegralR (f : (V → ℝ) → WithTop ℝ) : Prop :=
  MExchangeAxiomR f ∧ IntegralPolyhedralFunction f

end DiscreteConvex.MConvexFunctionsE


