-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SubDifferentialR
-- name    : DiscreteConvex_MConvexFunctionsD_SubDifferentialR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:34.693984+00:00
-- url     : https://prove2.me/theorems/9bd72e19-e334-405b-adcf-713e993b6e1c
-- title:
--   SubDifferentialR
-- statement:
--   The subdifferential $\partial_{\mathbb R} f(x)$ of a real-domain function at a real point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R f(x)` of a real-domain function at a real point (cf. Eq. (3.23)). -/
def SubDifferentialR (f : (V → ℝ) → WithTop ℝ) (x : V → ℝ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ y : V → ℝ, f y - f x ≥ (((∑ v, p v * (y v - x v)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsD


