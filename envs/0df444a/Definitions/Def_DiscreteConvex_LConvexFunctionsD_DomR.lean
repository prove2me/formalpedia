-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
-- name    : DiscreteConvex_LConvexFunctionsD_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:07.600001+00:00
-- url     : https://prove2.me/theorems/c0e014c1-0f48-4b0a-b7f1-d50746292c2b
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of a real-valued function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsD


