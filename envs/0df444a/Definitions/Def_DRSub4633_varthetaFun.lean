-- Prove2me | Definitions.Def_DRSub4633_varthetaFun
-- name    : DRSub4633_varthetaFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:17.472149+00:00
-- url     : https://prove2.me/theorems/3c4ba397-81ef-4cc8-91c1-501e1c59dfe3
-- title:
--   The weight $\vartheta(q)=q(1-q)/b$
-- statement:
--   For a real number $q$,
--   $$\vartheta(q)=\frac{q(1-q)}{b}.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (12), p.10

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The weight `ϑ(q) = q(1 − q)/b`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (12), p.10. -/
noncomputable def varthetaFun (q : ℝ) : ℝ := q * (1 - q) / bPar

end DRSub4633


