-- Prove2me | Definitions.Def_HOTrap_boxProj
-- name    : HOTrap_boxProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:05.718296+00:00
-- url     : https://prove2.me/theorems/edfa0444-036b-4d59-a399-588b335c418f
-- title:
--   Euclidean projection onto $[0,1]^d$
-- statement:
--   $\mathrm{proj}_{[0,1]^d}$ is the Euclidean projection onto the cube.
--
--   It enters the projected-gradient mapping.
--
--   **Formalization Note** It is defined as the coordinatewise clamp $x_i\mapsto\max(0,\min(1,x_i))$. A verification file proves that this point lies in the cube and is nearest to $x$ among all points of the cube.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, p.13

import Mathlib

namespace HOTrap

/-- **Euclidean projection onto `[0,1]^d`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, p.13 (`proj_{[0,1]^d}`).

**Formalization Note** This is the coordinatewise clamp `xᵢ ↦ max 0 (min 1 xᵢ)`. The verification file
proves that it lies in the cube and is a nearest point of the cube. -/
noncomputable def boxProj {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => max 0 (min 1 (x i)))

end HOTrap


