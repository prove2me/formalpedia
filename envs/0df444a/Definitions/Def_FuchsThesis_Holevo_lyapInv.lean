-- Prove2me | Definitions.Def_FuchsThesis_Holevo_lyapInv
-- name    : FuchsThesis_Holevo_lyapInv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:29.008719+00:00
-- url     : https://prove2.me/theorems/e44335e3-c2b0-4290-a2fc-712d2b0e09f8
-- title:
--   The super-operator $\mathcal L_{\hat\rho}$ of (3.181)
-- statement:
--   Let $\hat\rho$ be Hermitian with orthonormal eigenbasis $\{|j\rangle\}$ and eigenvalues $\lambda_j$. For an operator $\hat B$ with matrix elements $B_{jk}=\langle j|\hat B|k\rangle$, set
--
--   $$
--   \mathcal L_{\hat\rho}(\hat B) = \sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \frac{2}{\lambda_j+\lambda_k}\,B_{jk}\,|j\rangle\langle k| ,
--   $$
--
--   where the terms in the null subspace of $\hat\rho$ are set to zero. Where it exists, this is the solution of the Lyapunov equation $\tfrac12\big(\hat\rho\,\mathcal L_{\hat\rho}(\hat B)+\mathcal L_{\hat\rho}(\hat B)\,\hat\rho\big)=\hat B$ (3.177). The source writes the formula for $\hat B=\hat\Delta$; it is the operator that minimizes $J''(t)$ over measurements and defines $L''(t)=-\mathrm{tr}(\hat\Delta\,\mathcal L_{\hat\rho}(\hat\Delta))$.
--
--   **Formalization Note** With $U$ Mathlib's eigenvector unitary of $\hat\rho$, the value is $U M U^\dagger$ with $M_{jk}=2B_{jk}/(\lambda_j+\lambda_k)$ when $\lambda_j+\lambda_k\ne0$ and $M_{jk}=0$ otherwise. The value does not depend on the choice of eigenbasis. The formula is written for every operator $\hat B$, since (3.182) applies $\mathcal L_{\hat\rho}$ to a general $\hat B$. For a non-Hermitian $\hat\rho$ the value is a junk $0$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.181), p.70 (PDF p.79); (3.177), p.69 (PDF p.78)

import Mathlib
import Definitions.Def_FuchsThesis_Holevo_eigval
import Definitions.Def_FuchsThesis_Holevo_eigCoord

namespace FuchsThesis.Holevo

open Classical in
/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.181), p.70 (PDF p.79): the super-operator `𝓛_ρ̂`
("lowering" super-operator solving the Lyapunov equation `½(ρ̂ 𝓛_ρ̂(Â) + 𝓛_ρ̂(Â) ρ̂) = Â` (3.177)),
given in an orthonormal eigenbasis `{|j⟩}` of `ρ̂` with eigenvalues `λ_j` by
`𝓛_ρ̂(B̂) = ∑_{j,k | λ_j + λ_k ≠ 0} (2/(λ_j + λ_k)) B_jk |j⟩⟨k|`,
"where we have conveniently set the terms in the null subspace of `ρ̂` to be zero".

**Formalization Note.** With `U = IsHermitian.eigenvectorUnitary` (`ρ = U diag(λ) U†`) the value
is `U M U†` where `M_jk = 2 B_jk/(λ_j + λ_k)` if `λ_j + λ_k ≠ 0` and `M_jk = 0` otherwise, with
`B_jk = (U† B U)_jk` (`FuchsThesis.Holevo.eigCoord`). The source applies (3.181) to `B̂ = Δ̂`; the
same formula is written for any operator `B̂`, as the source's (3.182) uses `𝓛_ρ̂(B̂)`. The value
does not depend on the choice of eigenbasis (the weight `2/(λ_j + λ_k)` is constant on pairs of
eigenspaces). For a non-Hermitian `ρ` the value is the junk `0`. -/
noncomputable def lyapInv {d : Type} [Fintype d] [DecidableEq d] (ρ B : Matrix d d ℂ) :
    Matrix d d ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.of (fun j k => if eigval ρ j + eigval ρ k ≠ 0 then
        ((2 / (eigval ρ j + eigval ρ k) : ℝ) : ℂ) * eigCoord ρ B j k else 0) *
      star (h.eigenvectorUnitary : Matrix d d ℂ)
  else 0

end FuchsThesis.Holevo


