-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_AdmissiblePotentials
-- name    : DiscreteConvex_MConvexFunctionsD_AdmissiblePotentials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:21.49728+00:00
-- url     : https://prove2.me/theorems/e7a7ff04-08b0-41ad-ae26-54d1810d24ef
-- title:
--   AdmissiblePotentials
-- statement:
--   The set $D(\gamma)$ of admissible potentials of a distance function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set `D(γ)` of admissible potentials of a distance function, Eq. (5.3)-(5.4). -/
def AdmissiblePotentials (γ : V → V → WithTop ℝ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ u v, u ≠ v → ((p v - p u : ℝ) : WithTop ℝ) ≤ γ u v}

end DiscreteConvex.MConvexFunctionsD


