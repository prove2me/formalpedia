-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_DomZ
-- name    : DiscreteConvex_NetworkFlowsC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:25.421635+00:00
-- url     : https://prove2.me/theorems/51fbd7fa-8c29-4eaa-8695-7a68c4d42aca
-- title:
--   DomZ
-- statement:
--   The effective domain of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.NetworkFlowsC


