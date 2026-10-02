-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_DomR
-- name    : DiscreteConvex_NetworkFlowsC_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:37.685323+00:00
-- url     : https://prove2.me/theorems/b1b19322-bc4d-4592-b695-c4957e56bf15
-- title:
--   DomR
-- statement:
--   The effective domain of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.NetworkFlowsC


