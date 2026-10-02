-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ProjectionR
-- name    : DiscreteConvex_MConvexFunctionsD_ProjectionR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:59.509961+00:00
-- url     : https://prove2.me/theorems/3462d709-3b9e-4e60-8782-0e3ecd21ca84
-- title:
--   ProjectionR
-- statement:
--   The projection $f^U(y)=\inf\{f(z):z(w)=y(w),w\in U\}$ for real-domain $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue of Eq. (6.41).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue of Eq. (6.41)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The projection `f^U(y) = inf{f(z) : z(w) = y(w), w ∈ U}` for real-domain `f`. -/
noncomputable def ProjectionR (f : (V → ℝ) → WithTop ℝ) (U : Finset V) (y : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ z : V → ℝ, (∀ v ∈ U, z v = y v) ∧ L = f z}

end DiscreteConvex.MConvexFunctionsD


