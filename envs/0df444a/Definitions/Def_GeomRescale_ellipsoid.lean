-- Prove2me | Definitions.Def_GeomRescale_ellipsoid
-- name    : GeomRescale_ellipsoid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:10.142441+00:00
-- url     : https://prove2.me/theorems/16cb76e5-2ff4-4a13-99d6-6ff0baba1f63
-- title:
--   The ellipsoid $E(R)$
-- statement:
--   $$E(R) = \{x \in \mathbb{R}^n : x^{\mathsf T} R x \le 1\}.$$
--
--   The analysis shows that this ellipsoid contains $F_\mu$ throughout the algorithm.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.10

import Mathlib

namespace GeomRescale

/-- The ellipsoid `E(R) = {x ∈ ℝⁿ : xᵀRx ≤ 1}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §3.3, p.10). -/
def ellipsoid {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ (R.mulVec x) ≤ 1}

end GeomRescale


