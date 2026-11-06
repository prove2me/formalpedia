-- Prove2me | Definitions.Def_DRSub4633_thetaMinus
-- name    : DRSub4633_thetaMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:29.342205+00:00
-- url     : https://prove2.me/theorems/4d2c239e-b484-43bb-badd-0394eb436857
-- title:
--   The function $\theta_-(t)=\Gamma e^{s(t-1)}$
-- statement:
--   $$\theta_-(t)=\Gamma e^{s(t-1)}.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (22), p.12

import Mathlib
import Definitions.Def_DRSub4633_Gam
import Definitions.Def_DRSub4633_sPar

namespace DRSub4633

/-- **The function `θ₋(t) = Γe^(s(t−1))`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (22), p.12. -/
noncomputable def thetaMinus (t : ℝ) : ℝ := Gam * Real.exp (sPar * (t - 1))

end DRSub4633


