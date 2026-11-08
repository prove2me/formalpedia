-- Prove2me | Definitions.Def_GaussianSweep_simplexVec
-- name    : GaussianSweep_simplexVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:05.348317+00:00
-- url     : https://prove2.me/theorems/4f5d23a3-1266-484e-b82a-81528ba989d6
-- title:
--   Regular simplex vector $U^*$ in three variables
-- statement:
--   Let $w_k = (\cos\frac{2\pi k}{3}, \sin\frac{2\pi k}{3}) \in \mathbb R^2$, $k = 0, 1, 2$: three unit vectors at mutual angles $2\pi/3$, so $w_0 + w_1 + w_2 = 0$. For $g \in \mathbb R^2$ put $U^*_k(g) = \langle w_k, g\rangle$. When $g$ is a standard Gaussian vector in the plane, $U^* = (U^*_0, U^*_1, U^*_2)$ is the **regular simplex vector** in three variables: centered, with unit variances and all pairwise correlations $-\tfrac12$, and $U^*_0 + U^*_1 + U^*_2 = 0$.
--
--   **Formalization Note** Indices are $0, 1, 2$; any three unit vectors at mutual angles $2\pi/3$ give the same law.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 6.2, p.36 (PDF p.38); Section 8.3, p.49 (PDF p.51)

import Mathlib

namespace GaussianSweep

/-- The regular simplex vector in three variables, `U*_k = ⟨w_k, g⟩` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 6.2, p.36
(PDF p.38); Section 8.3, p.49 (PDF p.51)), realized as the projections of a planar point `g` onto
the three unit vectors `w_k = (cos(2πk/3), sin(2πk/3))`, `k = 0, 1, 2`, at mutual angles `2π/3`.

**Formalization Note** 0-based index `k : Fin 3`. For `g` standard Gaussian in `ℝ²` the vector
`(U*_0, U*_1, U*_2)` is centered with unit variances and pairwise correlations `−1/2`, and
`U*_0 + U*_1 + U*_2 = 0`. -/
noncomputable def simplexVec (k : Fin 3) (g : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) / 3) * g 0 + Real.sin (2 * Real.pi * ((k : ℕ) : ℝ) / 3) * g 1

end GaussianSweep


