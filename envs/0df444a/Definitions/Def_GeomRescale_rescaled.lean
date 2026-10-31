-- Prove2me | Definitions.Def_GeomRescale_rescaled
-- name    : GeomRescale_rescaled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:58.444116+00:00
-- url     : https://prove2.me/theorems/4c9981b2-5dce-4f95-b857-8732ba62ee8b
-- title:
--   The rescaling (10)
-- statement:
--   After a call of Algorithm 1 that returned $g_1, \dots, g_k$ and $x$, the matrix $R$ becomes
--
--   $$R' = \frac{1}{(1 + \varepsilon)^2}\Bigl(R + \sum_{i=1}^k \frac{x_i}{\|g_i\|_Q^2} g_i g_i^{\mathsf T}\Bigr),$$
--
--   with the norm of the old $Q$. Then $Q := (R')^{-1}$. The denominator is $(1 + \varepsilon)^2$, as Remark 3.7 stresses.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (10), p.10

import Mathlib
import Definitions.Def_GeomRescale_qnorm

namespace GeomRescale

/-- The rescaling (10) of Algorithm 2 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (10), p.10):
`R′ = (1/(1 + ε)²) (R + ∑_{i=1}^k (x_i/‖g_i‖²_Q) g_i g_iᵀ)`.

**Formalization Note.** `Q` is the matrix before the update, and `data` is the list of `(g_i, x_i)`
of the call just finished. The denominator is `(1 + ε)²`, not `1 + ε` (Remark 3.7). -/
noncomputable def rescaled {n : ℕ} (ε : ℝ) (Q R : Matrix (Fin n) (Fin n) ℝ)
    (data : List ((Fin n → ℝ) × ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  ((1 + ε) ^ 2)⁻¹ •
    (R + (data.map (fun p => (p.2 / qnorm Q p.1 ^ 2) • Matrix.vecMulVec p.1 p.1)).sum)

end GeomRescale


