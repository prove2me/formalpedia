-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR
-- name    : DiscreteConvex_LConvexFunctionsD_SubDifferentialR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:40.809129+00:00
-- url     : https://prove2.me/theorems/7b4f4c75-1c68-468a-9c93-5a106664fb89
-- title:
--   SubDifferentialR
-- statement:
--   The subdifferential $\partial_{\mathbb R} g(p)$ of a real-domain function at a real point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R g(p)` of a real-domain function at a real point. -/
def SubDifferentialR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : Set (V → ℝ) :=
  {x : V → ℝ | ∀ q : V → ℝ, g q - g p ≥ (((∑ v, x v * (q v - p v)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsD


