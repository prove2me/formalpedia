-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialRZ
-- name    : DiscreteConvex_LConvexFunctionsD_SubDifferentialRZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:44.966446+00:00
-- url     : https://prove2.me/theorems/7941e4b2-72db-4755-a364-dabfe5e1872d
-- title:
--   SubDifferentialRZ
-- statement:
--   The subdifferential $\partial_{\mathbb R} g(p)$ of an integer-domain function at an integer point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86)-analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R g(p)` of an integer-domain function at an integer point. -/
def SubDifferentialRZ (g : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : Set (V → ℝ) :=
  {x : V → ℝ | ∀ q : V → ℤ, g q - g p ≥ (((∑ v, x v * ((q v : ℝ) - (p v : ℝ))) : ℝ) : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsD


