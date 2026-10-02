-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron
-- name    : DiscreteConvex_NetworkFlowsB_IsPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:42.409345+00:00
-- url     : https://prove2.me/theorems/e60e98a5-4dda-4821-b32b-6ea488cc0747
-- title:
--   IsPolyhedron
-- statement:
--   A subset of $W^V$-indexed reals cut out by finitely many linear inequalities.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.80, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A subset of `Wⱽ`-indexed reals cut out by finitely many linear inequalities. -/
def IsPolyhedron {W : Type*} [Fintype W] (S : Set (W → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → W → ℝ) (b : Fin m → ℝ), S = {x | ∀ i, ∑ w, a i w * x w ≤ b i}

end DiscreteConvex.NetworkFlowsB


