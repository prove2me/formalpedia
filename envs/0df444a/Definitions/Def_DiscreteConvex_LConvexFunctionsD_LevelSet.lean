-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LevelSet
-- name    : DiscreteConvex_LConvexFunctionsD_LevelSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:51.314439+00:00
-- url     : https://prove2.me/theorems/b2c87ff0-500a-477c-b71d-7839d74f88db
-- title:
--   LevelSet
-- statement:
--   The level set $L(g,\alpha)=\{p\in\mathbb Z^V : g(p)\le\alpha\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Eq. (6.95)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Eq. (6.95)-analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The level set `L(g, α) = {p ∈ Zⱽ | g(p) ≤ α}`. -/
def LevelSet (g : (V → ℤ) → WithTop ℝ) (alpha : ℝ) : Set (V → ℤ) :=
  {p | g p ≤ (alpha : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsD


