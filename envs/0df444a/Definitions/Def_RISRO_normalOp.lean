-- Prove2me | Definitions.Def_RISRO_normalOp
-- name    : RISRO_normalOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:32:41.609718+00:00
-- url     : https://prove2.me/theorems/f8dde309-3137-4161-ae44-cb4b419fda30
-- title:
--   The operator $\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t$
-- statement:
--   Let $\mathcal A:\mathbb R^{p_1\times p_2}\to\mathbb R^n$, $\mathcal A(X)_i=\langle A_i,X\rangle$, with adjoint $\mathcal A^*(z)=\sum_i z_iA_i$. This is the normal operator of the least squares problem (10),
--
--   $$
--   W\mapsto \mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t(W),
--   $$
--
--   acting on triples.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 1, p.8, and Lemma 2, p.10

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_Lop
import Definitions.Def_RISRO_LopAdj

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The operator `L_t^* A^* A L_t` on `Ran(L_t^*)`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 1, p.8, and Lemma 2, p.10.

Formalization Note: `A` is given by its measurement matrices, `A(X)_i = ⟨A_i, X⟩`
(`observationOp`), `A^*(z) = ∑ z_i A_i` (`observationOpAdjoint`), display (2), p.1. -/
def normalOp {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (W : Triple p₁ p₂ r) : Triple p₁ p₂ r :=
  LopAdj U Uc V Vc (observationOpAdjoint A (observationOp A (Lop U Uc V Vc W)))

end RISRO


