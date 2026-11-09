-- Prove2me | Definitions.Def_QMAvsQCIP_epsInc
-- name    : QMAvsQCIP_epsInc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:35.119028+00:00
-- url     : https://prove2.me/theorems/b8c22297-c9eb-4585-b683-28cf6613d553
-- title:
--   Incompressibility error $\varepsilon_{\mathrm{inc}}(\lambda)=2^{-8\lambda^2}$
-- statement:
--   The incompressibility error of Eq. (7):
--   $$
--   \varepsilon_{\mathrm{inc}}(\lambda)=2^{-8\lambda^2}.
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 4.2, Eq. (7), p.19

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The incompressibility error `ε_inc(λ) = 2^{−8λ²}` (Eq. (7)).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 4.2, p.19 (PDF p.22): "ε_inc(λ) = 2^{−8λ²}". -/
noncomputable def epsInc (lam : ℕ) : ℝ := ((2 : ℝ) ^ (8 * lam ^ 2))⁻¹

end QMAvsQCIP


