-- Prove2me | Definitions.Def_DRSub4633_c1
-- name    : DRSub4633_c1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:20.84205+00:00
-- url     : https://prove2.me/theorems/d25fc23f-ec81-40f0-8c01-a126a1258c12
-- title:
--   The coefficient sum $c_1=1+1/b$
-- statement:
--   The number $c_1=1+1/b$. It is the sum of the coefficients $\chi_i$ in (16), which does not depend on the state because the dummy large coordinate has weight $q_1=1$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10, and Eq. (16), p.11

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The coefficient sum `c₁ = 1 + 1/b`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.10 and Eq. (16), p.11:
"the coefficient sum `c₁ = 1 + 1/b`". -/
noncomputable def c1 : ℝ := 1 + 1 / bPar

end DRSub4633


