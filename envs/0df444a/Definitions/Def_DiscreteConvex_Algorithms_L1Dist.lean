-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_L1Dist
-- name    : DiscreteConvex_Algorithms_L1Dist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:16.307505+00:00
-- url     : https://prove2.me/theorems/39ea1ad8-36c1-4883-8be1-2fa4aeb5d2e6
-- title:
--   $\ell^1$ distance between integer vectors
-- statement:
--   $\|x-y\|_1 = \sum_v |x(v)-y(v)|$, the $\ell^1$ distance between two integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282

import Mathlib

namespace DiscreteConvex.Algorithms

/-- The `ℓ¹` distance `‖x - y‖₁ = Σ_v |x(v) - y(v)|` between two integer vectors. -/
noncomputable def L1Dist {V : Type*} [Fintype V] (x y : V → ℤ) : ℕ :=
  ∑ v, (x v - y v).natAbs

end DiscreteConvex.Algorithms


