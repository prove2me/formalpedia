-- Prove2me | Definitions.Def_GaussianSweep_Supplement_simplexVec4
-- name    : GaussianSweep_Supplement_simplexVec4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:23.740213+00:00
-- url     : https://prove2.me/theorems/82f6bdf6-ea28-4659-9cc9-9af67a1adb27
-- title:
--   Regular simplex vector $U^*$ in four variables
-- statement:
--   Let $w_1,\dots,w_4 \in \mathbb R^3$ be unit vectors with $\langle w_i, w_j\rangle = -1/3$ for $i \ne j$ (the vertices of a regular tetrahedron inscribed in the unit sphere), and let $G$ be a standard Gaussian vector in $\mathbb R^3$. The **regular simplex vector in four variables** is $U^* = (U^*_1,\dots,U^*_4)$ with
--   $$
--   U^*_i = \langle w_i, G\rangle .
--   $$
--   It is centered, with unit variances, pairwise correlations $-1/3$, and $\sum_i U^*_i = 0$. Here the projections are given as functions of the point $g = G(\omega) \in \mathbb R^3$.
--
--   **Formalization Note** The tetrahedron is fixed as $w_i = s_i/\sqrt3$ with sign vectors $s_i = (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)$ (alternate vertices of a cube); any other choice is a rotation and gives the same law. Index $0$-based.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 6.2, p.36 (PDF p.38), d = 4

import Mathlib

namespace GaussianSweep.Supplement

/-- The regular simplex vector in four variables, `U*_k = ⟨w_k, g⟩`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 6.2, p.36 (PDF p.38), with `d = 4`), realized as the
projections of a point `g ∈ ℝ³` onto the four unit vectors
`w_k = (s_{k,0}, s_{k,1}, s_{k,2})/√3` with sign rows `(1,1,1)`, `(1,−1,−1)`, `(−1,1,−1)`,
`(−1,−1,1)` (alternate vertices of a cube, a regular tetrahedron inscribed in the unit sphere).

**Formalization Note** 0-based index `k : Fin 4`. The `w_k` are unit vectors with
`⟨w_i, w_j⟩ = −1/3` for `i ≠ j` and `Σ w_k = 0`; for `g` standard Gaussian in `ℝ³` the vector
`(U*_0, …, U*_3)` is centered with unit variances and pairwise correlations `−1/3`, as on p.36. -/
noncomputable def simplexVec4 (k : Fin 4) (g : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] k 0 * g 0 +
    ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] k 1 * g 1 +
    ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] k 2 * g 2) / Real.sqrt 3

end GaussianSweep.Supplement


