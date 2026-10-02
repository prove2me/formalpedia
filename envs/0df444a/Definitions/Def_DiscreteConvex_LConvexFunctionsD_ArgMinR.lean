-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
-- name    : DiscreteConvex_LConvexFunctionsD_ArgMinR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:28.940044+00:00
-- url     : https://prove2.me/theorems/61749db0-6d3d-40d9-ab8f-f7352a11ed00
-- title:
--   ArgMinR
-- statement:
--   The minimizer set of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a real-domain function. -/
def ArgMinR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.LConvexFunctionsD


