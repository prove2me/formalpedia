-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_ArgMinR
-- name    : DiscreteConvex_LConvexFunctionsC_ArgMinR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:18.887641+00:00
-- url     : https://prove2.me/theorems/b04e7828-bc0d-44a4-9729-4ca150a5a05a
-- title:
--   ArgMinR
-- statement:
--   The minimizer set of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a real-domain function. -/
def ArgMinR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.LConvexFunctionsC


