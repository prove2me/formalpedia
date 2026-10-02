-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_DomZ
-- name    : DiscreteConvex_AlgorithmsC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:17:49.455339+00:00
-- url     : https://prove2.me/theorems/c7511042-bc8b-4a9b-9639-e5cbbd802397
-- title:
--   DomZ
-- statement:
--   The effective domain of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of an integer-domain function. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | g x ≠ ⊤}

end DiscreteConvex.AlgorithmsC


