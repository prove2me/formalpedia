-- Prove2me | Definitions.Def_FreeSpencer_Supplement_opHq
-- name    : FreeSpencer_Supplement_opHq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:32:49.559384+00:00
-- url     : https://prove2.me/theorems/2979f40b-bb31-479f-8b46-a3c4d5a7d67e
-- title:
--   Negative density Hessian of the Tsallis-regularized potential
-- statement:
--   Fix $q,\theta\in\mathbb R$. At a positive definite density $S$, the negative Hessian of the Tsallis regularizer $r_{q,\theta}(S)=\frac{\theta}{1-q}\operatorname{Tr}S^{1-q}$ is the linear operator
--   $$\mathcal H^{\mathrm{original}}_{r}(X)=-\theta\,D(S^{-q})[X]=-\theta\,\frac{d}{dt}\Big|_{t=0}(S+tX)^{-q}$$
--   on symmetric directions $X$. Adding the negative Hessian of the fidelity term, $\mathcal H_f^{\mathrm{original}}=\mathcal L^*\mathcal K^{-1}\mathcal L$ with $\mathcal K=Z^{-1}(\cdot)M+M(\cdot)Z^{-1}$ and $\mathcal L=Z^{-1}(\cdot)Z^{-1}-\eta_C(\cdot)$ at $M=\eta_C(S)$ and the transport $Z$, gives the **negative density Hessian**
--   $$\mathcal H^{\mathrm{original}}=\mathcal H_f^{\mathrm{original}}+\mathcal H_r^{\mathrm{original}}.$$
--   Its inverse defines the local unconstrained response $\sum_a\frac12\langle B'_a,(\mathcal H^{\mathrm{original}})^{-1}B'_a\rangle$ used in Theorem 9.5. At $q=1/2$ it is the square-root operator of Lemma 5.2.
--
--   **Formalization Note** The derivative is taken along the line $S+tX$ in the matrix space; $(\cdot)^{-q}$ is the functional-calculus power `MatrixLewis.mpow`; $\mathcal H_f^{\mathrm{original}}$ is the published `FreeSpencer.opHf`.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), §8, p.58 (ℋ^original = ℋ_r^original + ℒ∗𝒦⁻¹ℒ); Lemma 9.1, p.58; Lemma 5.2 and eq. (5.5), pp.31–32

import Mathlib
import Definitions.Def_MatrixLewis_mpow
import Definitions.Def_FreeSpencer_transport
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer.Supplement

open FreeSpencer

/-- `H_{q,θ}^original = -θ D(S^{-q})[·]`, the negative Hessian of the Tsallis regularizer
`r_{q,θ}(S) = θ/(1-q) · Tr S^{1-q}` in the density, as a derivative along the line `S + tX`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer,
arXiv:2609.18914 (held file sha256 e1c1ba14…), §8, pp.56–58 (`ℋ_r^original`); Lemma 9.1, p.58;
the case `q = 1/2` is Lemma 5.2, p.32.

**Formalization Note** Used at `S ≻ 0` and symmetric `X` only. At `q = 1/2` this is the published
`FreeSpencer.opHtheta`. `deriv` is taken in the matrix space with the L2-operator norm. -/
noncomputable def opHq {ι : Type*} [Fintype ι] [DecidableEq ι] (q θ : ℝ) (S X : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  (-θ) • deriv (fun t : ℝ => MatrixLewis.mpow (-q) (S + t • X)) 0

/-- The negative density Hessian of the Tsallis-regularized potential,
`H^original = H_f^original + H_{q,θ}^original`, with `H_f^original = L∗K⁻¹L` the published
`FreeSpencer.opHf` at transport `Z` and `M = η_C(S)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer,
arXiv:2609.18914 (held file sha256 e1c1ba14…), p.58 (`ℋ^original = ℋ_r^original + ℒ∗𝒦⁻¹ℒ`); eq. (5.5), p.32. -/
noncomputable def opHqFull {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (S Z M X : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  opHf Ah C Z M X + opHq q θ S X

end FreeSpencer.Supplement


