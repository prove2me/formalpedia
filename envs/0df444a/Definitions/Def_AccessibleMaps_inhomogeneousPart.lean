-- Prove2me | Definitions.Def_AccessibleMaps_inhomogeneousPart
-- name    : AccessibleMaps_inhomogeneousPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:07:25.486062+00:00
-- url     : https://prove2.me/theorems/9f62a34c-0ea8-4328-948c-c976d33f5bff
-- title:
--   The inhomogeneous part $X(\rho)=\operatorname{tr}_B[U\,C(\rho)\,U^\dagger]$
-- statement:
--   For an affine assignment, a unitary $U$ and a matrix $\rho$, the **inhomogeneous part** is the $a\times a$ matrix
--   $$
--   X(\rho)=\operatorname{tr}_B\big[U\,C(\rho)\,U^\dagger\big],\qquad C(\rho)=E_{\mathcal V}(\rho)-\rho\otimes\omega(\rho).
--   $$
--   In Fano coordinates it is the second sum of Eq. (23), $\sum_\mu\sum_{i,j}\Gamma_{ij}\langle\mu|U\sigma^A_i\otimes\sigma^B_jU^\dagger|\mu\rangle=\vec\xi\cdot\vec\sigma^A$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (23), p.4 and the proof of Proposition 1, p.5

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment_correlation
import Definitions.Def_AccessibleMaps_reducedEvolution

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The inhomogeneous part `X(ρ) = tr_B [U C(ρ) U†]`, the image of the correlation term. For
Fano coefficients this is `∑_μ ∑_{ij} Γ_ij ⟨μ|U σ_i^A ⊗ σ_j^B U†|μ⟩`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (23), p.4 (PDF p.4) and the proof of
Proposition 1, p.5 (PDF p.5). -/
noncomputable def inhomogeneousPart (E : AffineAssignment a H)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) (ρ : Matrix a a ℂ) : Matrix a a ℂ :=
  reducedEvolution U (E.correlation ρ)

end AccessibleMaps


