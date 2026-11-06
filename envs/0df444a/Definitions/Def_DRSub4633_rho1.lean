-- Prove2me | Definitions.Def_DRSub4633_rho1
-- name    : DRSub4633_rho1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:46.776012+00:00
-- url     : https://prove2.me/theorems/097ae5bd-0fb3-4e35-a908-13aa4383c7a4
-- title:
--   The weight $\rho_1=c_1\lambda+\kappa$
-- statement:
--   $$\rho_1(t)=c_1\lambda(t)+\kappa(t).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.12

import Mathlib
import Definitions.Def_DRSub4633_c1
import Definitions.Def_DRSub4633_lam
import Definitions.Def_DRSub4633_kappa

namespace DRSub4633

/-- **The weight `ρ₁ = c₁λ + κ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.12: "With `c₁ = 1 + 1/b`, let
`ρ₁ = c₁λ + κ`." -/
noncomputable def rho1 (t : ℝ) : ℝ := c1 * lam t + kappa t

end DRSub4633


