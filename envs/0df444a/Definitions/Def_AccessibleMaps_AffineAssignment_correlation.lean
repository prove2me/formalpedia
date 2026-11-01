-- Prove2me | Definitions.Def_AccessibleMaps_AffineAssignment_correlation
-- name    : AccessibleMaps_AffineAssignment_correlation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:40.906537+00:00
-- url     : https://prove2.me/theorems/7a3f83e5-2b3d-47b5-8382-e7c81f2a0284
-- title:
--   The correlation term $C(\rho)=E_{\mathcal V}(\rho)-\rho\otimes\omega(\rho)$ (Eq. (14))
-- statement:
--   For an affine assignment and a matrix $\rho$, the **correlation term** is
--   $$
--   C(\rho)=E_{\mathcal V}(\rho)-\rho\otimes\omega(\rho),
--   $$
--   the second term of the decomposition $\tau_{AB}=\rho\otimes\omega+(\tau_{AB}-\rho\otimes\omega)$ of Eq. (14). In Fano coordinates its coefficients are the correlation tensor $\Gamma_{ij}$ of Eq. (4).
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (14), p.3, with Eq. (4), p.1

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment_marginal
import Definitions.Def_AccessibleMaps_tensorOp

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The correlation term `C(ρ) = E_𝒱(ρ) - ρ ⊗ ω(ρ)` of the decomposition (14).

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (14), p.3 (PDF p.3):
"τ_AB = ρ ⊗ ω + (τ_AB − ρ ⊗ ω)". Its coefficients in the generators are the `Γ_ij` of Eq. (4). -/
noncomputable def AffineAssignment.correlation (E : AffineAssignment a H) (ρ : Matrix a a ℂ) :
    Composite a H →L[ℂ] Composite a H :=
  E.assign ρ - tensorOp ρ (E.marginal ρ)

end AccessibleMaps


