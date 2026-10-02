-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ArgMin
-- name    : DiscreteConvex_AlgorithmsC_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:10.053823+00:00
-- url     : https://prove2.me/theorems/9757f633-9fe6-4295-9a31-8c6154771b7b
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.AlgorithmsC


