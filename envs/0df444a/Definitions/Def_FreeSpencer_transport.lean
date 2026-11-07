-- Prove2me | Definitions.Def_FreeSpencer_transport
-- name    : FreeSpencer_transport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:52.664118+00:00
-- url     : https://prove2.me/theorems/29914948-7731-4594-bde5-7aed1fa1d18b
-- title:
--   The transport and the operators $K$, $L$, $H_f$, $H_\theta$
-- statement:
--   At $S,M\succ0$ the transport is the positive definite solution of $ZMZ=S$, namely $Z=M^{-1/2}(M^{1/2}SM^{1/2})^{1/2}M^{-1/2}$. The operators of Lemma 5.2 are
--   $$K=Z^{-1}(\cdot)M+M(\cdot)Z^{-1},\quad L=Z^{-1}(\cdot)Z^{-1}-\eta_C(\cdot),\quad H_f^{\mathrm{original}}=L^*K^{-1}L,\quad H_\theta^{\mathrm{original}}=-\theta D(S^{-1/2})[\cdot],$$
--   and the negative density Hessian is $H^{\mathrm{original}}=H_f^{\mathrm{original}}+H_\theta^{\mathrm{original}}$.
--
--   **Formalization Note** $L$ is self-adjoint for the trace pairing, so $L^*$ is written as $L$. $K^{-1}$ is the inverse in the ring of linear maps on the full real matrix space, and `lemma_5_2` asserts that $K$ is invertible.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, pp.31–32

import Mathlib
import Definitions.Def_MatrixLewis_mpow
import Definitions.Def_FreeSpencer_covMap
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The transport `Z = M^{-1/2} (M^{1/2} S M^{1/2})^{1/2} M^{-1/2}`, the positive definite solution
of `Z M Z = S`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), proof of Lemma 5.2, p.32.

**Formalization Note** Used at `S, M ≻ 0` only. -/
noncomputable def transport {ι : Type*} [Fintype ι] [DecidableEq ι] (S M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  MatrixLewis.mpow (-(1 / 2)) M * MatrixLewis.mpow (1 / 2) (MatrixLewis.mpow (1 / 2) M * S * MatrixLewis.mpow (1 / 2) M) * MatrixLewis.mpow (-(1 / 2)) M

/-- The operator `K = Z⁻¹(·)M + M(·)Z⁻¹` of Lemma 5.2, on the full real matrix space.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, p.31. -/
noncomputable def opK {ι : Type*} [Fintype ι] [DecidableEq ι] (Z M : Matrix ι ι ℝ) :
    Module.End ℝ (Matrix ι ι ℝ) :=
  LinearMap.mulLeft ℝ Z⁻¹ ∘ₗ LinearMap.mulRight ℝ M + LinearMap.mulLeft ℝ M ∘ₗ LinearMap.mulRight ℝ Z⁻¹

/-- The operator `L = Z⁻¹(·)Z⁻¹ - η_C(·)` of Lemma 5.2.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, p.31.

**Formalization Note** `L` is self-adjoint for the trace pairing, since `η_C` is (p.18) when the `Âᵢ`
are symmetric, so the source's `L∗` is written `opL` in the statements. -/
noncomputable def opL {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (Z X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Z⁻¹ * X * Z⁻¹ - covMap Ah C X

/-- `H_f^original = L∗ K⁻¹ L`, eq. (5.5). Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), p.32. -/
noncomputable def opHf {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ)
    (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (Z M X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  opL Ah C Z (Ring.inverse (opK Z M) (opL Ah C Z X))

/-- `H_θ^original = -θ D(S^{-1/2})[·]`, the negative Hessian of `2θ Tr √S`, on symmetric directions.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, p.32. -/
noncomputable def opHtheta {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ) (S X : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  (-θ) • deriv (fun t : ℝ => MatrixLewis.mpow (-(1 / 2)) (S + t • X)) 0

/-- The negative density Hessian `H^original = H_f^original + H_θ^original`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, p.32. -/
noncomputable def opH {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (θ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (S Z M X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  opHf Ah C Z M X + opHtheta θ S X

end FreeSpencer


