-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_spec
-- name    : OptimalSpectrum_Entangled_spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:06.166813+00:00
-- url     : https://prove2.me/theorems/4e14789b-f11b-475a-b794-00ac7682c0c2
-- title:
--   Sorted spectrum $\mathrm{spec}(A)$ of a Hermitian matrix
-- statement:
--   For a Hermitian matrix $A\in\mathbb C^{d\times d}$, $\mathrm{spec}(A)\in\mathbb R^d$ is its eigenvalue vector, listed in nonincreasing order, with multiplicities and zero eigenvalues retained:
--
--   $$\mathrm{spec}(A)=(\lambda_1,\dots,\lambda_d),\qquad \lambda_1\ge\lambda_2\ge\cdots\ge\lambda_d .$$
--
--   This is the object the spectrum estimation problem asks for: the target of Theorem 1.1 is $\mathrm{spec}(\rho)$ for a density matrix $\rho$.
--
--   **Formalization Note** The vector is Mathlib's sorted eigenvalue list `IsHermitian.eigenvalues₀`, reindexed to `Fin d`; the unsorted `IsHermitian.eigenvalues` is not used. On a non-Hermitian matrix, where the paper never applies $\mathrm{spec}$, the value is the zero vector.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §4 Preliminaries (unnumbered), p. 11 (PDF p. 13)

import Mathlib

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **Sorted spectrum `spec(A)`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §4 Preliminaries (unnumbered), printed p. 11 (PDF p. 13): "For a Hermitian matrix A,
let spec(A) denote its eigenvalue vector, listed in nonincreasing order and with zero eigenvalues
retained."

**Formalization Note.** The value is Mathlib's sorted eigenvalue list `IsHermitian.eigenvalues₀`
(nonincreasing, multiplicities and zeros kept), reindexed from `Fin (Fintype.card (Fin d))` to
`Fin d`. The unsorted `IsHermitian.eigenvalues` is deliberately not used. On a non-Hermitian matrix,
where the paper never applies `spec`, the value is the zero vector. -/
noncomputable def spec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Fin d → ℝ :=
  if h : A.IsHermitian then fun i => h.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm i)
  else 0

end OptimalSpectrum.Entangled


