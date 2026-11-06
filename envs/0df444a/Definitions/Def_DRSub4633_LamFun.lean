-- Prove2me | Definitions.Def_DRSub4633_LamFun
-- name    : DRSub4633_LamFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:02.56921+00:00
-- url     : https://prove2.me/theorems/445015b7-0693-49bf-84f0-c7e2abbf803f
-- title:
--   The weight $\Lambda(q)=1+b+\vartheta(q)$
-- statement:
--   For a real number $q$,
--   $$\Lambda(q)=1+b+\vartheta(q)=\mathfrak c(q)(b+1-q).$$
--   It is the coefficient of the last prefix path in the constant term (32) and of the tail $W$ in (47).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (12), p.10

import Mathlib
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_varthetaFun

namespace DRSub4633

/-- **The weight `Λ(q) = 1 + b + ϑ(q)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (12), p.10
(where also `Λ(q) = 𝔠(q)(b + 1 − q)`). -/
noncomputable def LamFun (q : ℝ) : ℝ := 1 + bPar + varthetaFun q

end DRSub4633


