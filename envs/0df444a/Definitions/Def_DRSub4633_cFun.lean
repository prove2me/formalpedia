-- Prove2me | Definitions.Def_DRSub4633_cFun
-- name    : DRSub4633_cFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:20.515139+00:00
-- url     : https://prove2.me/theorems/042ae3e2-4fab-47a2-9758-c39841b64293
-- title:
--   The weight $\mathfrak c(q)=1+q/b$
-- statement:
--   For a real number $q$,
--   $$\mathfrak c(q)=1+\frac qb .$$
--   It weights the gradient terms of the large coordinates and appears in the scalar averaging inequality (47).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (12), p.10

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The weight `𝔠(q) = 1 + q/b`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (12), p.10. -/
noncomputable def cFun (q : ℝ) : ℝ := 1 + q / bPar

end DRSub4633


