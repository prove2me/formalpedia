-- Prove2me | Definitions.Def_DRSub4633_thetaPlus
-- name    : DRSub4633_thetaPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:04:48.384909+00:00
-- url     : https://prove2.me/theorems/89d876ac-337d-4524-8c7a-606d61d8f179
-- title:
--   The function $\theta_+$
-- statement:
--   $$\theta_+(t)=e^{st}\Big[\Gamma e^{-s}-b+b\int_0^t\rho_1(r)e^{-sr}\,dr\Big].$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (21), p.12

import Mathlib
import Definitions.Def_DRSub4633_Gam
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_rho1

namespace DRSub4633

/-- **The function `θ₊`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (21), p.12:
`θ₊(t) = e^(st) [Γe^(−s) − b + b ∫_0^t ρ₁(r) e^(−sr) dr]`. -/
noncomputable def thetaPlus (t : ℝ) : ℝ :=
  Real.exp (sPar * t) *
    (Gam * Real.exp (-sPar) - bPar + bPar * ∫ r in (0 : ℝ)..t, rho1 r * Real.exp (-(sPar * r)))

end DRSub4633


