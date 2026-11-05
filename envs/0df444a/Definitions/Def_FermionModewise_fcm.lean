-- Prove2me | Definitions.Def_FermionModewise_fcm
-- name    : FermionModewise_fcm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:22.750006+00:00
-- url     : https://prove2.me/theorems/4c77c280-6e86-4291-8480-cc482b635b50
-- title:
--   Fermion covariance matrix $M_{\alpha\beta}=\frac1{2i}\langle[\gamma_\alpha,\gamma_\beta]\rangle$
-- statement:
--   For a family of operators $(\gamma_\alpha)_{\alpha\in\nu}$ on $\mathbb C^\iota$ and a vector $\psi$, the **fermion covariance matrix** (FCM) is the real matrix
--   $$M_{\alpha\beta}=\operatorname{Re}\Big(\frac1{2i}\,\langle\psi,[\gamma_\alpha,\gamma_\beta]\,\psi\rangle\Big),\qquad [X,Y]=XY-YX .$$
--   For the quadratures of a state $\psi$ this is the paper's $M_{\alpha\beta}=\frac1{2i}\langle[\gamma_\alpha,\gamma_\beta]\rangle_\rho$ with $\rho=|\psi\rangle\langle\psi|$.
--
--   The FCM is the object on which the whole proof of the main result operates: canonical transformations act on it by $M\mapsto OMO^T$, and purity reads $M^2=-\mathbb 1$.
--
--   **Formalization Note.** The prefactor is $1/(2i)$ as printed. For a Hermitian family the bracketed number is already real (milestone `fcm_real_antisymm`), so the real part loses nothing. The family is arbitrary, so the definition applies to rotated quadratures $O\gamma$ as well. No normalization of $\psi$ is applied; statements use unit vectors.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (8), p.5

import Mathlib

open Matrix

namespace FermionModewise

/-- **Fermion covariance matrix (FCM)** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (8), p.5):
`M_αβ = (1/2i) ⟨[γ_α, γ_β]⟩_ψ` for a family of operators `γ` and a state vector `ψ`.

**Formalization Note.** The expectation in the pure state `ψ` is `⟨ψ, X ψ⟩ = star ψ ⬝ᵥ (X *ᵥ ψ)`
(no normalization is applied; it is used for unit `ψ`). The prefactor is `1/(2i)`, as printed,
not `i/2`. For a Hermitian family the number is real (milestone `fcm_real_antisymm`), so taking
the real part `.re` loses nothing. The family `γ` is generic, so the same definition applies to
the quadratures `majorana b` and to any rotated family `Oγ`. -/
noncomputable def fcm {ι ν : Type} [Fintype ι] (γ : ν → Matrix ι ι ℂ) (ψ : ι → ℂ) :
    Matrix ν ν ℝ :=
  Matrix.of fun α β =>
    ((1 / (2 * Complex.I)) * (star ψ ⬝ᵥ ((γ α * γ β - γ β * γ α) *ᵥ ψ))).re

end FermionModewise


