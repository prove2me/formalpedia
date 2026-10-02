-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMin
-- name    : DiscreteConvex_NetworkFlowsB_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:41.239423+00:00
-- url     : https://prove2.me/theorems/ef1bc6f8-90af-418d-a908-2958548edf09
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared, integer domain.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared, integer domain

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, f x ≤ f y}

end DiscreteConvex.NetworkFlowsB


