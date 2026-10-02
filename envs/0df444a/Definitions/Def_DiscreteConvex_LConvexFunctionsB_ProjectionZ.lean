-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_ProjectionZ
-- name    : DiscreteConvex_LConvexFunctionsB_ProjectionZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:08.479586+00:00
-- url     : https://prove2.me/theorems/dccb40b6-9fb1-4ed8-a1e2-331eebc3d48c
-- title:
--   ProjectionZ
-- statement:
--   The projection $g_U(y)=\inf\{g(z):z(w)=y(w),\ w\in U\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143-144, Eq. (6.41)/(6.45)-analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143-144, Eq. (6.41)/(6.45)-analogue

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The projection `g_U(y) = inf\{g(z) : z(w)=y(w),\ w \in U\}`, Eq. (6.41)/(6.45)-analogue. -/
noncomputable def ProjectionZ (g : (V → ℤ) → WithTop ℝ) (U : Set V) (y : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ z : V → ℤ, (∀ w ∈ U, z w = y w) ∧ L = g z}

end DiscreteConvex.LConvexFunctionsB


