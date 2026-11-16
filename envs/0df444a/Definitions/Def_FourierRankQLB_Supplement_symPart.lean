-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_symPart
-- name    : FourierRankQLB_Supplement_symPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:13:38.334199+00:00
-- url     : https://prove2.me/theorems/d4ea1370-9d5e-42de-af33-bca763889cc2
-- title:
--   Symmetric part $S_Q = (Q + Q^\top)/2$ of an orthogonal matrix
-- statement:
--   For an orthogonal matrix $Q \in O(n)$, its **symmetric part** is the real symmetric matrix
--
--   $$
--   S_Q = \frac{Q + Q^\top}{2}.
--   $$
--
--   On each real two-dimensional rotation plane of $Q$ with eigenangle $\theta$, $S_Q$ acts as $\cos\theta$ times the identity, so the spectrum of $S_Q$ records the eigenangles of $Q$. A determinant $-1$ forces the eigenvalue $-1$ of $S_Q$.
--
--   **Formalization Note** The module also records that $S_Q$ is Hermitian (symmetric). Its smallest eigenvalue $\lambda_{\min}(S_Q)$ (Theorem 3.9) is taken with the published general definition `BlockBochner.lamMin`.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.3, p.20

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open Matrix

namespace FourierRankQLB

namespace Supplement

/-- The symmetric part `S_Q = (Q + Qᵀ)/2` of an orthogonal matrix `Q ∈ O(n)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.3, p. 20. -/
noncomputable def symPart {n : ℕ} (Q : Od n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • ((Q : Matrix (Fin n) (Fin n) ℝ) + (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ)

/-- `S_Q` is a real symmetric (Hermitian) matrix. -/
theorem symPart_isHermitian {n : ℕ} (Q : Od n) : (symPart Q).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [symPart, Matrix.transpose_add, add_comm]

end Supplement

end FourierRankQLB


