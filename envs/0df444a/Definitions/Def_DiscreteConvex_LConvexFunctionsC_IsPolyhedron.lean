-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedron
-- name    : DiscreteConvex_LConvexFunctionsC_IsPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:10.477876+00:00
-- url     : https://prove2.me/theorems/bf8053a4-9625-4fe7-994d-6a6ed191c144
-- title:
--   IsPolyhedron
-- statement:
--   A subset of $\mathbb R^W$ cut out by finitely many linear inequalities.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A subset of `Rᵂ` cut out by finitely many linear inequalities. -/
def IsPolyhedron {W : Type*} [Fintype W] (S : Set (W → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → W → ℝ) (b : Fin m → ℝ), S = {x | ∀ i, ∑ w, a i w * x w ≤ b i}

end DiscreteConvex.LConvexFunctionsC


