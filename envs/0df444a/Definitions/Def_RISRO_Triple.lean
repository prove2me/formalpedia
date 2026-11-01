-- Prove2me | Definitions.Def_RISRO_Triple
-- name    : RISRO_Triple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:57.758327+00:00
-- url     : https://prove2.me/theorems/843bbeb8-8fd9-4f23-a0db-796cb54278e4
-- title:
--   The space $\mathrm{Ran}(\mathcal L_t^*)$ as triples $(W_0,W_1,W_2)$
-- statement:
--   The operator $\mathcal L_t$ of the paper acts on block matrices
--
--   $$
--   \begin{bmatrix} W_0 & W_2\\ W_1 & 0\end{bmatrix},\qquad W_0\in\mathbb R^{r\times r},\quad W_1\in\mathbb R^{(p_1-r)\times r},\quad W_2\in\mathbb R^{r\times(p_2-r)},
--   $$
--
--   with a zero bottom-right block. Such a block matrix is recorded as the triple $(W_0,W_1,W_2)$.
--
--   **Formalization Note.** The zero block is not stored. Addition and subtraction are componentwise, which agrees with the block matrices.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, display (9), p.7

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The domain `Ran(L_t^*)` of (9): a triple `(W₀, W₁, W₂)` stands for the block matrix
`[W₀ W₂; W₁ 0]` with `W₀ ∈ ℝ^{r×r}`, `W₁ ∈ ℝ^{(p₁-r)×r}`, `W₂ ∈ ℝ^{r×(p₂-r)}`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, display (9), p.7.

Formalization Note: the zero bottom-right block is not stored. Vector-space operations are
componentwise and agree with those of the block matrices. -/
abbrev Triple (p₁ p₂ r : ℕ) : Type :=
  Matrix (Fin r) (Fin r) ℝ × Matrix (Fin (p₁ - r)) (Fin r) ℝ × Matrix (Fin r) (Fin (p₂ - r)) ℝ

end RISRO


