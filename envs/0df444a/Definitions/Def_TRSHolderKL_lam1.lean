-- Prove2me | Definitions.Def_TRSHolderKL_lam1
-- name    : TRSHolderKL_lam1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:46.043088+00:00
-- url     : https://prove2.me/theorems/ee1c1425-9af9-4a87-8141-15b286b49adf
-- title:
--   The smallest eigenvalue $\lambda_1$ of $A$
-- statement:
--   For a symmetric matrix $A$ with spectral decomposition $A=P\Lambda P^T$, $\Lambda=\mathrm{Diag}(\lambda)$, $\lambda_1\le\dots\le\lambda_n$, the number $\lambda_1$ is the smallest eigenvalue of $A$. The sign of $\lambda_1$ separates the convex TRS ($\lambda_1\ge0$) from the nonconvex one ($\lambda_1<0$).
--
--   **Formalization Note** Defined as the infimum of the real spectrum of $A$. For symmetric $A$ and $n\ge1$ the spectrum is finite and nonempty, so this is its least element (checked in a verification file). All theorems of the mission assume $n\ge2$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.3

import Mathlib

namespace TRSHolderKL

/-- `λ₁`, the smallest eigenvalue of the symmetric matrix `A`,
Jiang and Li, arXiv:1911.11955v2, p.3 (`A = PΛPᵀ`, `Λ = Diag(λ)`, `λ₁ ≤ ⋯ ≤ λₙ`).

**Formalization Note.** The infimum of the real spectrum of `A`. For a symmetric `A` with
`n ≥ 1` the spectrum is finite and nonempty, so this is its least element (checked in the
verification file). -/
noncomputable def lam1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf (spectrum ℝ A)

end TRSHolderKL


