-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinR
-- name    : DiscreteConvex_NetworkFlowsB_ArgMinR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:22.359088+00:00
-- url     : https://prove2.me/theorems/8b08f73d-77db-4f80-bc78-6317db6d257d
-- title:
--   ArgMinR
-- statement:
--   The minimizer set of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimizer set of a real-domain function. -/
def ArgMinR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.NetworkFlowsB


