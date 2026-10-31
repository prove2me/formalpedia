-- Prove2me | Definitions.Def_AuditEvasion_Gamma
-- name    : AuditEvasion_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:03.770041+00:00
-- url     : https://prove2.me/theorems/b583409c-a132-47ae-baf6-15b77c74bb26
-- title:
--   Eq. (12), p.1850 — the function $\Gamma(t;h)$
-- statement:
--   For the model parameters, equation (12) of Theorem 2 uses
--
--   $$\Gamma(t;h)=(\lambda+\theta)\big[F-(k+F)e^{-\lambda t}\big]-\lambda h\big[1-e^{-(\lambda+\theta)t}\big].$$
--
--   Its positive root $t^\star$ is the length of the audit-free period that opens each cycle of the optimal policy under perfect evasion.
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, Theorem 2, eq. (12), p.1850

import Mathlib
import Definitions.Def_AuditEvasion_Model

namespace AuditEvasion

/-- The function of equation (12), Oper. Res. 72(5) (2024), Theorem 2, p.1850:
`Γ(t; h) = (λ + θ)[F − (k + F) e^{−λt}] − λh[1 − e^{−(λ+θ)t}]`. -/
noncomputable def Gamma (p : Params) (t : ℝ) : ℝ :=
  (p.lam + p.theta) * (p.F - (p.k + p.F) * Real.exp (-p.lam * t)) -
    p.lam * p.h * (1 - Real.exp (-(p.lam + p.theta) * t))

end AuditEvasion


