-- Prove2me | Definitions.Def_GeomRescale_norm2
-- name    : GeomRescale_norm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:34.362568+00:00
-- url     : https://prove2.me/theorems/5d6b5346-0cfc-4586-a6a6-1dd6516e1fe3
-- title:
--   The Euclidean norm $\|z\|_2$
-- statement:
--   For a vector $z \in \mathbb{R}^V$,
--
--   $$\|z\|_2 = \Bigl(\sum_{v \in V} |z(v)|^2\Bigr)^{1/2}.$$
--
--   This norm defines the complexity parameter $L_{f,2}$ and the unit ball $\mathbb{B}^n$.
--
--   **Formalization Note** Lean's `‖·‖` on `Fin n → ℝ` is the sup norm, so the Euclidean norm is written out.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3

import Mathlib

namespace GeomRescale

/-- The `ℓ₂`-norm `‖z‖₂ = (∑_{v ∈ V} |z(v)|²)^{1/2}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3).

**Formalization Note.** Lean's `‖·‖` on `Fin n → ℝ` is the sup norm, so the Euclidean norm is
written out and that notation is never used. -/
noncomputable def norm2 {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  √(∑ v, z v ^ 2)

end GeomRescale


