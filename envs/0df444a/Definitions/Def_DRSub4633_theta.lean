-- Prove2me | Definitions.Def_DRSub4633_theta
-- name    : DRSub4633_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:06:52.86376+00:00
-- url     : https://prove2.me/theorems/9fb9e877-559a-471d-a06f-0c16ebd60aae
-- title:
--   The function $\theta=\min\{\theta_+,\theta_-\}$
-- statement:
--   $$\theta(t)=\min\{\theta_+(t),\theta_-(t)\}.$$
--   Together with $\rho_1$ it defines the budget $B(\tau)$ of the scalar averaging inequality.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (22), p.12

import Mathlib
import Definitions.Def_DRSub4633_thetaPlus
import Definitions.Def_DRSub4633_thetaMinus

namespace DRSub4633

/-- **The function `θ = min{θ₊, θ₋}`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (22), p.12. -/
noncomputable def theta (t : ℝ) : ℝ := min (thetaPlus t) (thetaMinus t)

end DRSub4633


