-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
-- name    : DiscreteConvex_LConvexFunctionsC_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:55.903987+00:00
-- url     : https://prove2.me/theorems/6581c573-0498-4f5c-9861-5523aeead3b8
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of a real-valued function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsC


