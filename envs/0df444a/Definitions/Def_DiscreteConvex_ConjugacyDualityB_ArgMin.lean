-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMin
-- name    : DiscreteConvex_ConjugacyDualityB_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:26:37.39097+00:00
-- url     : https://prove2.me/theorems/54973967-a76e-4acf-a0fd-9ee2e202dc5f
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, f x ≤ f y}

end DiscreteConvex.ConjugacyDualityB


