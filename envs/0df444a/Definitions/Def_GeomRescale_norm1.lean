-- Prove2me | Definitions.Def_GeomRescale_norm1
-- name    : GeomRescale_norm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:13.197836+00:00
-- url     : https://prove2.me/theorems/3e9c5bb7-8442-44f8-a0af-b4e32003316f
-- title:
--   The $\ell_1$-norm $\|z\|_1$
-- statement:
--   For a vector $z \in \mathbb{R}^V$,
--
--   $$\|z\|_1 = \sum_{v \in V} |z(v)|.$$
--
--   This norm defines the complexity parameter $L_f$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3

import Mathlib

namespace GeomRescale

/-- The `ℓ₁`-norm `‖z‖₁ = ∑_{v ∈ V} |z(v)|` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3). -/
def norm1 {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ∑ v, |z v|

end GeomRescale


