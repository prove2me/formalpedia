-- Prove2me | Definitions.Def_DRSub4633_UWeight
-- name    : DRSub4633_UWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:06:07.915199+00:00
-- url     : https://prove2.me/theorems/f646497d-f9c1-48f5-bf5e-830c988923d9
-- title:
--   The remaining weight $U=\rho_1\mathbf 1_{(z,1]}$
-- statement:
--   $$U(t)=\rho_1(t)-\psi(t)=\rho_1(t)\,\mathbf 1_{(z,1]}(t).$$
--   It weights the small-coordinate increments $\nu_t$ in the field (24).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (23), p.12

import Mathlib
import Definitions.Def_DRSub4633_zCross
import Definitions.Def_DRSub4633_rho1

namespace DRSub4633

/-- **The remaining weight `U(t) = ρ₁(t) − ψ(t) = ρ₁(t) 1_(z,1](t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072,
Section 4.1, Eq. (23), p.12. -/
noncomputable def UWeight (t : ℝ) : ℝ := if zCross < t ∧ t ≤ 1 then rho1 t else 0

end DRSub4633


