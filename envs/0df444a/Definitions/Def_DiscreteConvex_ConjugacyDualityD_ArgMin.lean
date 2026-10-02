-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_ArgMin
-- name    : DiscreteConvex_ConjugacyDualityD_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:32.514481+00:00
-- url     : https://prove2.me/theorems/a9146696-40c0-4a99-828d-5bd3b22fba1c
-- title:
--   ArgMin
-- statement:
--   The minimizer set of an integer-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of an integer-domain function. -/
def ArgMin (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | ∀ y, f x ≤ f y}

end DiscreteConvex.ConjugacyDualityD


