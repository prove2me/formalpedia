-- Prove2me | Definitions.Def_QMAvsQCIP_gammaL
-- name    : QMAvsQCIP_gammaL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:30.232265+00:00
-- url     : https://prove2.me/theorems/cbe503db-47ec-413b-b559-db3db4c8b4fa
-- title:
--   Rate $\gamma(\lambda)=\lceil\lambda/12\rceil$
-- statement:
--   The incompressibility rate of Eq. (7):
--   $$
--   \gamma(\lambda)=\lceil\lambda/12\rceil .
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 4.2, Eq. (7), p.19

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The incompressibility rate `γ(λ) = ⌈λ/12⌉` (Eq. (7)).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 4.2, p.19 (PDF p.22): "γ(λ) = ⌈λ/12⌉, ε_inc(λ) = 2^{−8λ²},
t_inc(λ, s) = ⌈(s + 8λ²)/γ(λ)⌉. (7)" -/
noncomputable def gammaL (lam : ℕ) : ℕ := ⌈(lam : ℝ) / 12⌉₊

end QMAvsQCIP


