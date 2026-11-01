-- Prove2me | Definitions.Def_LowRankMEG_mlog
-- name    : LowRankMEG_mlog
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:22.517965+00:00
-- url     : https://prove2.me/theorems/da34227a-1a18-4425-a49c-3bbb6bda92c6
-- title:
--   The matrix logarithm $\log(X)$
-- statement:
--   For a symmetric positive definite matrix with eigen-decomposition $X=V\operatorname{diag}(\lambda_1,\dots,\lambda_n)V^\top$, the **matrix logarithm** is
--   $$
--   \log(X)=V\operatorname{diag}(\log\lambda_1,\dots,\log\lambda_n)V^\top.
--   $$
--   It is the gradient of the negative von Neumann entropy, up to the identity.
--
--   **Formalization Note** The definition is Mathlib's continuous functional calculus, `cfc Real.log X`. A finite spectrum makes every function continuous on it, so this is the spectral formula. Because `Real.log 0 = 0`, on a singular $X\succeq0$ it is the compact logarithm $V_X\log(\Lambda_X)V_X^\top$, which also realizes the paper's convention $0\log(0):=0$ in $X\log(X)$.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, §2.1, p.5; the convention at p.5

import Mathlib

namespace LowRankMEG

/-- **The matrix logarithm** `log(X) = V diag(log λ₁, …, log λ_n) Vᵀ` of `X = V diag(λ₁, …, λ_n) Vᵀ`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, §2.1, p.5.

**Formalization Note.** Mathlib's continuous functional calculus: on a finite spectrum every function
is continuous, so this is the spectral formula (`Matrix.IsHermitian.cfc_eq`). The paper defines `log`
for `X ≻ 0` and adds the convention `0 log(0) := 0` on p.5. Since `Real.log 0 = 0`, for `X ⪰ 0` singular
`mlog X` is the compact logarithm `V_X log(Λ_X) V_Xᵀ`, and `X * mlog X` carries exactly that convention.
No statement of this mission applies `mlog` to the second argument of `bregman` at a singular matrix. -/
noncomputable def mlog {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc Real.log X

end LowRankMEG


