-- Prove2me | Definitions.Def_DRSub4633_PqPrefix
-- name    : DRSub4633_PqPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:06.034443+00:00
-- url     : https://prove2.me/theorems/ca71ee9e-70ec-449e-8ecc-436c338b0909
-- title:
--   The prefix integral $P_q(T)$
-- statement:
--   $$P_q(T)=\int_0^TF_q(t)\,dt.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix A, Eq. (118), p.43

import Mathlib
import Definitions.Def_DRSub4633_FqInt

namespace DRSub4633

/-- **The prefix integral `P_q(T) = ∫_0^T F_q(t) dt`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix A, Eq. (118), p.43. -/
noncomputable def PqPrefix (q T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, FqInt q t

end DRSub4633


