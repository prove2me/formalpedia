-- Prove2me | Definitions.Def_HOTrap_cubeBoundary
-- name    : HOTrap_cubeBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:47:20.013479+00:00
-- url     : https://prove2.me/theorems/d325ab85-3541-44d1-95aa-9e2a0c437296
-- title:
--   Boundary relative to the cube
-- statement:
--   For a compact set $R\subseteq[0,1]^d$, the boundary in the subspace topology of the cube is
--   $$
--   \partial_{[0,1]^d}R=R\setminus\mathrm{int}_{[0,1]^d}(R).
--   $$
--
--   The boundary of the whole cube is empty, so physical faces need no certificate.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.15

import Mathlib
import Definitions.Def_HOTrap_cubeInterior

namespace HOTrap

/-- **`∂_{[0,1]^d} R = R \ int_{[0,1]^d}(R)`**, the boundary of a compact `R ⊆ [0,1]^d` in the
subspace topology of the cube. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.15. -/
def cubeBoundary {d : ℕ} (R : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := R \ cubeInterior R

end HOTrap


