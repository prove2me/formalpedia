-- Prove2me | Definitions.Def_HOTrap_cubeInterior
-- name    : HOTrap_cubeInterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:09.915993+00:00
-- url     : https://prove2.me/theorems/890a66bc-b185-42ff-bc4c-25614b68d84f
-- title:
--   Interior relative to the cube
-- statement:
--   For a compact set $R\subseteq[0,1]^d$, $\mathrm{int}_{[0,1]^d}(R)$ is the interior of $R$ in the subspace topology of the cube: the points $z\in R$ with an open neighbourhood $U$ in $\mathbb R^d$ such that $U\cap[0,1]^d\subseteq R$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.15

import Mathlib
import Definitions.Def_GeomDRSub_cube

namespace HOTrap

/-- **`int_{[0,1]^d}(R)`**: the interior of `R ⊆ [0,1]^d` in the subspace topology of the cube.
Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.15.

**Formalization Note** A point `z ∈ R` is interior when some open `U ∋ z` of `ℝ^d` has
`U ∩ [0,1]^d ⊆ R`. -/
def cubeInterior {d : ℕ} (R : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {z | z ∈ R ∧ ∃ U, IsOpen U ∧ z ∈ U ∧ U ∩ GeomDRSub.cube d ⊆ R}

end HOTrap


