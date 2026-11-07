-- Prove2me | Definitions.Def_FreeSpencer_covMap
-- name    : FreeSpencer_covMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:59.022202+00:00
-- url     : https://prove2.me/theorems/35f5389c-f9e6-4b99-8926-24543bb438fb
-- title:
--   The covariance map $\eta_C$ and the matrices $\hat A(u)$
-- statement:
--   For a covariance $C$ on the coefficient space and a family $\hat A_1,\dots,\hat A_\ell$, the covariance map is
--   $$\eta_C(X)=\sum_{i,j}C_{ij}\hat A_iX\hat A_j,$$
--   and $\hat A(u)=\sum_iu_i\hat A_i$ for a coefficient vector $u$. Factoring $C$ shows $\eta_C$ is completely positive and self-adjoint for the trace pairing.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (2.1), p.18

import Mathlib

namespace FreeSpencer

/-- The covariance map `η_C(X) = ∑_{i,j} C_{ij} Âᵢ X Âⱼ`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (2.1), p.18. -/
def covMap {ι : Type*} [Fintype ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ i, ∑ j, C i j • (Ah i * X * Ah j)

/-- The matrix `Â(u) = ∑ᵢ uᵢ Âᵢ` of a coefficient vector `u`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 2.1, p.18. -/
def aHat {ι : Type*} [Fintype ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (u : Fin ℓ → ℝ) : Matrix ι ι ℝ :=
  ∑ i, u i • Ah i

end FreeSpencer


