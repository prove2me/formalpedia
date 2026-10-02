-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedron
-- name    : DiscreteConvex_MConvexFunctionsC_IsPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:51.443899+00:00
-- url     : https://prove2.me/theorems/65175da7-3acc-46bd-975a-bd92485cff7f
-- title:
--   IsPolyhedron
-- statement:
--   A subset of $\mathbb R^W$ cut out by finitely many linear inequalities.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, supporting Theorem 6.47.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion, supporting Theorem 6.47

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A subset of `Wⱽ`-indexed reals cut out by finitely many linear inequalities. -/
def IsPolyhedron {W : Type*} [Fintype W] (S : Set (W → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → W → ℝ) (b : Fin m → ℝ), S = {x | ∀ i, ∑ w, a i w * x w ≤ b i}

end DiscreteConvex.MConvexFunctionsC


