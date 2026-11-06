-- Prove2me | Definitions.Def_FourierRankQLB_AQ
-- name    : FourierRankQLB_AQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:48.435815+00:00
-- url     : https://prove2.me/theorems/6ca15434-e348-4dfd-8753-605bfd9dec29
-- title:
--   The matrix $A_Q=(\tfrac12+2g_d)I_d+\tfrac14(Q+Q^T)$
-- statement:
--   For $Q\in O(d)$, the symmetric matrix
--   $$
--   A_Q=\Bigl(\frac12+2g_d\Bigr)I_d+\frac14\,(Q+Q^T).
--   $$
--   Its spectrum lies in $[2g_d,1+2g_d]$, and a reflection in $Q$ (eigenvalue $-1$) gives $A_Q$ the eigenvalue $2g_d$. This is how the sign of $\det Q$ reaches the bottom of the spectrum.
--
--   **Formalization Note** Eq. (31) is taken as the definition.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eqs. (30)–(31), p.24

import Mathlib
import Definitions.Def_FourierRankQLB_Od
import Definitions.Def_FourierRankQLB_gd

open Matrix

namespace FourierRankQLB

/-- The positive-definite matrix `A_Q = (1/2 + 2g_d) I_d + (Q + Qᵀ)/4` of Eq. (31).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eqs. (30)–(31), p. 24.

**Formalization Note.** Eq. (31) is taken as the definition. Eq. (30) is the same matrix, written as
`(1 + 2g_d) I_d - H_Q` with `H_Q = (I_d - S_Q)/2`. -/
noncomputable def AQ {d : ℕ} (Q : Od d) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 + 2 * gd d) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (1 / 4 : ℝ) • ((Q : Matrix (Fin d) (Fin d) ℝ) + (Q : Matrix (Fin d) (Fin d) ℝ)ᵀ)

end FourierRankQLB


