-- Prove2me | Definitions.Def_QMAvsQCIP_delta
-- name    : QMAvsQCIP_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:41.34293+00:00
-- url     : https://prove2.me/theorems/76b01e25-10cb-49bb-8774-4fda724096aa
-- title:
--   Marking probability $\delta=2^{-\lceil\lambda/12\rceil}$
-- statement:
--   The marking probability of the NO distribution and the base of the incompressibility bounds:
--   $$
--   \delta=\delta(\lambda)=2^{-\lceil\lambda/12\rceil}=2^{-\gamma(\lambda)} .
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, Eq. (13), p.24; Theorem 3, p.19

import Definitions.Def_QMAvsQCIP_gammaL

set_option autoImplicit false

namespace QMAvsQCIP

/-- The marking probability `δ = 2^{−⌈λ/12⌉} = 2^{−γ(λ)}`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "Set p = λ^{−4}, δ = 2^{−⌈λ/12⌉}. (13)";
Theorem 3, p.19 (PDF p.22): "set δ = 2^{−⌈λ/12⌉}". -/
noncomputable def delta (lam : ℕ) : ℝ := ((2 : ℝ) ^ gammaL lam)⁻¹

end QMAvsQCIP


