-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_DomZ
-- name    : DiscreteConvex_NetworkFlowsB_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:52.005613+00:00
-- url     : https://prove2.me/theorems/a67315e2-c0bb-43f6-a558-ef52c9f36717
-- title:
--   DomZ
-- statement:
--   The effective domain of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The effective domain of an integer-domain function. -/
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.NetworkFlowsB


