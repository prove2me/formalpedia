-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_DomR
-- name    : DiscreteConvex_NetworkFlowsB_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:43.549747+00:00
-- url     : https://prove2.me/theorems/3b58555e-e933-4cbe-ba36-b2d92337d620
-- title:
--   DomR
-- statement:
--   The effective domain of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The effective domain of a real-domain function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.NetworkFlowsB


