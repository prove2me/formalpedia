-- Prove2me | Definitions.Def_FuchsThesis_Holevo_eigCoord
-- name    : FuchsThesis_Holevo_eigCoord
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:19.025796+00:00
-- url     : https://prove2.me/theorems/4583310e-10bf-4c88-9d52-be5970df2710
-- title:
--   Matrix elements $X_{jk}=\langle j|\hat X|k\rangle$ in an eigenbasis of $\hat\rho$
-- statement:
--   For a Hermitian operator $\hat\rho$ with orthonormal eigenbasis $\{|j\rangle\}$ (eigenvalues $\lambda_j$) and any operator $\hat X$, the matrix elements of $\hat X$ in that basis are
--
--   $$
--   X_{jk} = \langle j|\hat X|k\rangle .
--   $$
--
--   The source uses $\Delta_{jk}=\langle j|\hat\Delta|k\rangle$ for the difference operator $\hat\Delta=\hat\rho_1-\hat\rho_0$.
--
--   **Formalization Note** The eigenbasis is given by the columns of Mathlib's `IsHermitian.eigenvectorUnitary` $U$ (so $\hat\rho=U\,\mathrm{diag}(\lambda)\,U^\dagger$), and the matrix of elements is $U^\dagger \hat X U$. When eigenvalues repeat the basis is not unique, but every quantity of the mission built from it (sums $\sum_{j,k} f(\lambda_j,\lambda_k)|X_{jk}|^2$ and the operator (3.181)) does not depend on the choice. For a non-Hermitian $\hat\rho$ the value is a junk $0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, p.67 (PDF p.76) before (3.160); p.69 (PDF p.78) before (3.179)

import Mathlib

namespace FuchsThesis.Holevo

open Classical in
/-- Fuchs, arXiv:quant-ph/9601020v1, p.67 (PDF p.76) before (3.160) and p.69 (PDF p.78) before
(3.179): the matrix elements `X_jk = ⟨j|X̂|k⟩` of an operator `X̂` in an orthonormal eigenbasis
`{|j⟩}` of the Hermitian operator `ρ̂` (so `Δ_jk = ⟨j|Δ̂|k⟩`).

**Formalization Note.** For Hermitian `ρ` the eigenbasis is the columns of Mathlib's
`IsHermitian.eigenvectorUnitary U` (`ρ = U diag(λ) U†`), so the matrix of elements is `U† X U`;
column `j` of `U` has eigenvalue `FuchsThesis.Holevo.eigval ρ j`. The eigenbasis is not unique
when `ρ̂` has repeated eigenvalues, but every quantity of this mission built from it (sums of
`f(λ_j, λ_k) |X_jk|²` and the operator (3.181)) does not depend on the choice. For a non-Hermitian
`ρ` the value is the junk `0`. -/
noncomputable def eigCoord {d : Type} [Fintype d] [DecidableEq d] (ρ X : Matrix d d ℂ) :
    Matrix d d ℂ :=
  if h : ρ.IsHermitian then
    star (h.eigenvectorUnitary : Matrix d d ℂ) * X * (h.eigenvectorUnitary : Matrix d d ℂ)
  else 0

end FuchsThesis.Holevo


