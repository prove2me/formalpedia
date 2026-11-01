-- Prove2me | Definitions.Def_AccessibleMaps_AffineAssignment_assign
-- name    : AccessibleMaps_AffineAssignment_assign
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:02.861747+00:00
-- url     : https://prove2.me/theorems/88074893-ec4c-4d94-a34c-63b6daef4a22
-- title:
--   The extended state $E_{\mathcal V}(\rho)=g+G\rho$
-- statement:
--   For an affine assignment $(\mathcal V,g,G)$ and an $a\times a$ matrix $\rho$, the **extended state** is the operator
--   $$
--   E_{\mathcal V}(\rho)=g+G\rho
--   $$
--   on $\mathbb C^{a}\otimes\mathcal H$. For $\rho\in\mathcal V$ it is the joint state $\tau_{AB}$ assigned to the system state $\rho$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (5), p.1 and Eq. (21), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The extended state `E_𝒱(ρ) = g + G ρ`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (5), p.1 (PDF p.1) and Eq. (21), p.4 (PDF p.4). -/
noncomputable def AffineAssignment.assign (E : AffineAssignment a H) (ρ : Matrix a a ℂ) :
    Composite a H →L[ℂ] Composite a H :=
  E.g + E.G ρ

end AccessibleMaps


