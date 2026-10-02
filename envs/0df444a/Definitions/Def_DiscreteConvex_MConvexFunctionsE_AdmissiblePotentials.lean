-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_AdmissiblePotentials
-- name    : DiscreteConvex_MConvexFunctionsE_AdmissiblePotentials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:01.76798+00:00
-- url     : https://prove2.me/theorems/51fba58d-0790-4297-a417-3ec0ca06dd1a
-- title:
--   AdmissiblePotentials
-- statement:
--   The set $D(\gamma)$ of admissible potentials of a distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set `D(γ)` of admissible potentials of a distance function. -/
def AdmissiblePotentials (γ : V → V → WithTop ℝ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ u v, u ≠ v → ((p v - p u : ℝ) : WithTop ℝ) ≤ γ u v}

end DiscreteConvex.MConvexFunctionsE


