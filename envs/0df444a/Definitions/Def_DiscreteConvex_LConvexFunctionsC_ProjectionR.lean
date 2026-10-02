-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_ProjectionR
-- name    : DiscreteConvex_LConvexFunctionsC_ProjectionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:21.395976+00:00
-- url     : https://prove2.me/theorems/c61e2dc6-180c-4dcc-add5-148ab32feefb
-- title:
--   ProjectionR
-- statement:
--   The projection $g_U(y)=\inf\{g(z):z(w)=y(w),\ w\in U\}$ for real-domain $g$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143-144, Eq. (6.41)/(6.45)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143-144, Eq. (6.41)/(6.45)-analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The projection `g_U(y) = inf\{g(z) : z(w)=y(w),\ w \in U\}` for real-domain `g`. -/
noncomputable def ProjectionR (g : (V → ℝ) → WithTop ℝ) (U : Set V) (y : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ z : V → ℝ, (∀ w ∈ U, z w = y w) ∧ L = g z}

end DiscreteConvex.LConvexFunctionsC


