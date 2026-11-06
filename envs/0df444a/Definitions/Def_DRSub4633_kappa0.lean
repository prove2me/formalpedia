-- Prove2me | Definitions.Def_DRSub4633_kappa0
-- name    : DRSub4633_kappa0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:36.988587+00:00
-- url     : https://prove2.me/theorems/be3f05fe-b3e5-4546-96cb-bce15315f66d
-- title:
--   The weight $\kappa_0=b\mathbf 1_{[0,t_0)}$
-- statement:
--   $$\kappa_0(t)=b\,\mathbf 1_{[0,t_0)}(t).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.11

import Mathlib
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_t0

namespace DRSub4633

/-- **The weight `κ₀(t) = b 1_[0,t₀)(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.11 (before (19)). -/
noncomputable def kappa0 (t : ℝ) : ℝ := if 0 ≤ t ∧ t < t0 then bPar else 0

end DRSub4633


