-- Prove2me | Definitions.Def_RISRO_tripleNorm
-- name    : RISRO_tripleNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:42.376831+00:00
-- url     : https://prove2.me/theorems/cb6806fc-4c13-44b5-b0d5-0dbe7eff01fd
-- title:
--   Frobenius norm on $\mathrm{Ran}(\mathcal L_t^*)$
-- statement:
--   For a triple $W=(W_0,W_1,W_2)$ the norm is
--
--   $$
--   \|W\|_F=\bigl(\|W_0\|_F^2+\|W_1\|_F^2+\|W_2\|_F^2\bigr)^{1/2},
--   $$
--
--   the Frobenius norm of the block matrix $\begin{bmatrix} W_0 & W_2\\ W_1 & 0\end{bmatrix}$.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 2, p.10, and display (12), p.8

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The Frobenius norm of the block matrix `[W₀ W₂; W₁ 0]`:
`‖W‖_F = (‖W₀‖_F² + ‖W₁‖_F² + ‖W₂‖_F²)^{1/2}`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 2, p.10, and display (12), p.8 (the Frobenius
norm on `Ran(L_t^*)`). -/
noncomputable def tripleNorm {p₁ p₂ r : ℕ} (W : Triple p₁ p₂ r) : ℝ :=
  Real.sqrt (frobeniusNorm W.1 ^ 2 + frobeniusNorm W.2.1 ^ 2 + frobeniusNorm W.2.2 ^ 2)

end RISRO


