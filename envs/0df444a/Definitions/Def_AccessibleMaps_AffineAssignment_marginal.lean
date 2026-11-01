-- Prove2me | Definitions.Def_AccessibleMaps_AffineAssignment_marginal
-- name    : AccessibleMaps_AffineAssignment_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:27.202036+00:00
-- url     : https://prove2.me/theorems/f8df1ed0-6d05-4ee5-a3c5-51f925d43f72
-- title:
--   The environment marginal $\omega(\rho)=\operatorname{tr}_A E_{\mathcal V}(\rho)$
-- statement:
--   For an affine assignment and a matrix $\rho$, the **environment marginal** is
--   $$
--   \omega(\rho)=\operatorname{tr}_A E_{\mathcal V}(\rho),
--   $$
--   an operator on $\mathcal H$. It may depend on $\rho$ (affinely); only in the linear case of Eq. (13) is it independent of $\rho$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1 and Eq. (21), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment_assign
import Definitions.Def_AccessibleMaps_trA

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The marginal state of the environment, `ω(ρ) = tr_A E_𝒱(ρ)`. It may depend on `ρ`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1) and Eq. (21), p.4 (PDF p.4). -/
noncomputable def AffineAssignment.marginal (E : AffineAssignment a H) (ρ : Matrix a a ℂ) :
    H →L[ℂ] H :=
  trA (E.assign ρ)

end AccessibleMaps


