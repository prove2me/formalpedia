-- Prove2me | Definitions.Def_SelfSelReg_eigDesc
-- name    : SelfSelReg_eigDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:42.664456+00:00
-- url     : https://prove2.me/theorems/5240da16-b436-4b9f-928a-16b5484edfed
-- title:
--   Eigenvalues of a symmetric matrix in nonincreasing order, indexed from $1$
-- statement:
--   For a real symmetric $m\times m$ matrix $M$ write $\lambda_1(M)\ge\lambda_2(M)\ge\dots\ge\lambda_m(M)$ for its eigenvalues in nonincreasing order, counted with multiplicity, and set $\lambda_h(M)=0$ for $h=0$ and $h>m$.
--
--   The convention $\lambda_{m+1}(M)=0$ is the one Proposition 6.8 uses ("we understand $\hat\lambda_{p+1}=0$ and $\lambda_{q+1}(\Lambda)=0$") to define the largest eigengap.
--
--   **Formalization Note** $\lambda_h(M)$ is Mathlib's antitone `eigenvalues₀` at index $h-1$.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 6.8, p.39 (PDF p.42); Algorithm 6.2, p.39 (PDF p.42)

import Mathlib

namespace SelfSelReg

/-- **Eigenvalues in nonincreasing order, indexed from `1`**, with the convention `λ_h = 0` outside
`1 ≤ h ≤ m` (Proposition 6.8 and Algorithm 6.2).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 6.8, p.39 (PDF p.42): "Write the eigenvalues in
nonincreasing order … where we understand λ̂_{p+1} = 0 and λ_{q+1}(Λ) = 0."

For a symmetric real `m × m` matrix `M`, `eigDesc hM h = λ_h(M)` for `h = 1, …, m`, the `h`-th largest
eigenvalue counted with multiplicity (Mathlib's antitone `eigenvalues₀` at `h − 1`), and `0` for
`h = 0` and `h > m`. -/
noncomputable def eigDesc {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.IsHermitian) (h : ℕ) :
    ℝ :=
  if hh : 1 ≤ h ∧ h ≤ m then hM.eigenvalues₀ ⟨h - 1, by simp; omega⟩ else 0

end SelfSelReg


