-- Prove2me | Definitions.Def_GeomRescale_unitQ
-- name    : GeomRescale_unitQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:37.869627+00:00
-- url     : https://prove2.me/theorems/096cd954-d808-4e43-90d9-1f955419305e
-- title:
--   The normalized vector $g/\|g\|_Q$
-- statement:
--   The vector $g/\|g\|_Q$ used in Algorithm 1.
--
--   **Formalization Note** The page divides by $\|g\|_Q$ without excluding $g = 0$, which occurs for $f \equiv 0$. The formalization reads $g/\|g\|_Q := 0$ for $g = 0$. With this reading the identity $y = \sum_i x_i g_i/\|g_i\|_Q$ keeps its form, and $y = 0$ still certifies $0 \in B(f_\mu)$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, lines 2, 11, 12, p.8

import Mathlib
import Definitions.Def_GeomRescale_qnorm

namespace GeomRescale

/-- The normalized vector `g/‖g‖_Q` of Algorithm 1 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, lines 2, 11, 12, p.8).

**Formalization Note.** The page divides by `‖g‖_Q` without excluding `g = 0`, and `g = 0` does
occur: for `f ≡ 0` the vertex of line 2 is `0`. The formalization reads `g/‖g‖_Q := 0` for `g = 0`,
which is what Lean's `(‖g‖_Q)⁻¹ • g` gives. With that reading the output identity
`y = ∑ xᵢ gᵢ/‖gᵢ‖_Q` keeps its form and `y = 0` still certifies `0 ∈ B(f_μ)`. -/
noncomputable def unitQ {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  (qnorm Q g)⁻¹ • g

end GeomRescale


