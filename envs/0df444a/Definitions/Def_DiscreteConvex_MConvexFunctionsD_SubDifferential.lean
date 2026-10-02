-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferential
-- name    : DiscreteConvex_MConvexFunctionsD_SubDifferential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:25.503572+00:00
-- url     : https://prove2.me/theorems/607eb06d-ef1d-44da-b6e8-649049ff74b5
-- title:
--   SubDifferential
-- statement:
--   The subdifferential $\partial_{\mathbb R} f(x)$ of an integer-domain function at an integer point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R f(x)` of an integer-domain function at an integer point, Eq. (6.86). -/
def SubDifferential (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ y : V → ℤ, f y - f x ≥ (((∑ v, p v * ((y v : ℝ) - (x v : ℝ))) : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsD


