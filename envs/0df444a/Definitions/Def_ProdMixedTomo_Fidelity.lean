-- Prove2me | Definitions.Def_ProdMixedTomo_Fidelity
-- name    : ProdMixedTomo_Fidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:13:46.190492+00:00
-- url     : https://prove2.me/theorems/343ddf6a-5083-442c-9d32-1a4243eb94eb
-- title:
--   Fidelity $F(\rho,\sigma)=(\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho})^2$
-- statement:
--   For density matrices $\rho,\sigma$ the (squared) **fidelity** is
--   $$
--   F(\rho,\sigma)=\Bigl(\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\,\sqrt\rho}\Bigr)^2 ,
--   $$
--   where $\sqrt A=U\operatorname{diag}(\sqrt{\lambda_i})U^*$ for $A=U\operatorname{diag}(\lambda_i)U^*$ positive semidefinite. It is used in the analysis of the reduction (Lemma 3.5 and the Fuchs–van de Graaf step).
--
--   **Formalization Note** The square root is the spectral one, with `Real.sqrt` applied to each eigenvalue; the fidelity is the square of the real part of the trace, which is a nonnegative real for density matrices.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15)

import Mathlib

namespace ProdMixedTomo

/-!
# Fidelity

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15):
`F(ρ, σ) = (tr √(√ρ σ √ρ))²` (the squared fidelity).

**Formalization Note.** The square root of a Hermitian matrix `A = U diag(λ) U*` is
`U diag(√λ) U*` (spectral theorem, `Real.sqrt` of each eigenvalue); on positive semidefinite
matrices it is the PSD square root. The fidelity is the square of the real part of
`tr √(√ρ σ √ρ)`, a nonnegative real for density matrices.
-/

/-- The spectral square root `U diag(√λ) U*` of a Hermitian matrix (`0` if not Hermitian). -/
noncomputable def psdSqrt {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) :
    Matrix κ κ ℂ :=
  if h : A.IsHermitian then
    (h.eigenvectorUnitary : Matrix κ κ ℂ) *
      Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix κ κ ℂ)
  else 0

/-- The (squared) fidelity `F(ρ, σ) = (tr √(√ρ σ √ρ))²`. -/
noncomputable def fidelity {κ : Type*} [Fintype κ] [DecidableEq κ] (ρ σ : Matrix κ κ ℂ) : ℝ :=
  ((psdSqrt (psdSqrt ρ * σ * psdSqrt ρ)).trace.re) ^ 2

end ProdMixedTomo


