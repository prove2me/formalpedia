-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
-- name    : DiscreteConvex_ConjugacyDualityC_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:40:59.442858+00:00
-- url     : https://prove2.me/theorems/d1224e44-1a68-47e6-bd5f-4764e60d1bdf
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, f x ≤ f y}

end DiscreteConvex.ConjugacyDualityC


