-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SubDifferentialR
-- name    : DiscreteConvex_MConvexFunctionsE_SubDifferentialR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:05.262396+00:00
-- url     : https://prove2.me/theorems/1fd2e5d0-568a-44f1-b9be-3db32c09f4b3
-- title:
--   SubDifferentialR
-- statement:
--   The subdifferential $\partial_{\mathbb R} f(x)$ of a real-domain function at a real point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R f(x)` of a real-domain function at a real point. -/
def SubDifferentialR (f : (V → ℝ) → WithTop ℝ) (x : V → ℝ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ y : V → ℝ, f y - f x ≥ (((∑ v, p v * (y v - x v)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsE


