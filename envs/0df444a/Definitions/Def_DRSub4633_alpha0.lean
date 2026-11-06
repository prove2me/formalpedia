-- Prove2me | Definitions.Def_DRSub4633_alpha0
-- name    : DRSub4633_alpha0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:31.473132+00:00
-- url     : https://prove2.me/theorems/861f8aa6-45cd-4ad1-b83f-3d5552d7e9dd
-- title:
--   The coefficient $\alpha_0=\Gamma^{-1}$
-- statement:
--   The approximation coefficient
--   $$\alpha_0=\Gamma^{-1}=\frac{54440750000}{117486474169}>0.463378.$$
--   It also equals $4b/(2b+1)^2$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (8), p.9

import Mathlib
import Definitions.Def_DRSub4633_Gam

namespace DRSub4633

/-- **The coefficient `α₀ = Γ⁻¹`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (8), p.9:
"`α₀ = Γ⁻¹ = 54440750000/117486474169 > 0.463378`". -/
noncomputable def alpha0 : ℝ := Gam⁻¹

end DRSub4633


