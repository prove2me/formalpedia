-- Prove2me | Definitions.Def_DRSub4633_psi
-- name    : DRSub4633_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:06:44.52043+00:00
-- url     : https://prove2.me/theorems/228d1b63-15c5-49ba-bdd6-b70add58178f
-- title:
--   The weight $\psi=\rho_1\mathbf 1_{[0,z]}$
-- statement:
--   $$\psi(t)=\rho_1(t)\,\mathbf 1_{[0,z]}(t).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.12

import Mathlib
import Definitions.Def_DRSub4633_zCross
import Definitions.Def_DRSub4633_rho1

namespace DRSub4633

/-- **The weight `ψ(t) = ρ₁(t) 1_[0,z](t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.12. -/
noncomputable def psi (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ zCross then rho1 t else 0

end DRSub4633


