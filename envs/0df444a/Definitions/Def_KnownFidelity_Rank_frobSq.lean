-- Prove2me | Definitions.Def_KnownFidelity_Rank_frobSq
-- name    : KnownFidelity_Rank_frobSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:07.038916+00:00
-- url     : https://prove2.me/theorems/9ea5fc98-05da-484a-8a5d-704cb1022039
-- title:
--   Squared Frobenius norm $\|G\|_F^2$
-- statement:
--   For a complex matrix $G$, $\|G\|_F^2=\sum_{i,j}|G_{ij}|^2$. In §5.4, $R_b=\|G_b\|_F^2$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §2, p. 4 (PDF p. 6); §5.4, Eq. (40), p. 17 (PDF p. 19)

import Mathlib

namespace KnownFidelity.Rank

/-- **Squared Frobenius norm** `‖G‖_F² = Σ_{i,j} |G_ij|²`.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §2, printed p. 4 (PDF p. 6) ("∥X∥_F = ∥X∥₂ for the Frobenius norm"), and §5.4,
Eq. (40), printed p. 17 (PDF p. 19): "R_b = ∥G_b∥²_F". -/
noncomputable def frobSq {m n : Type*} [Fintype m] [Fintype n] (G : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖G i j‖ ^ 2

end KnownFidelity.Rank


