-- Prove2me | Definitions.Def_DSICCompComp_Supplement_lpRevenue
-- name    : DSICCompComp_Supplement_lpRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:27:45.971077+00:00
-- url     : https://prove2.me/theorems/1accefb6-91a6-4292-a274-75038d61697d
-- title:
--   Expected revenue $\sum_v f(v)\sum_i p_i(v)$
-- statement:
--   The objective of the DSIC revenue LP is the expected revenue of $(x, p)$,
--
--   $$
--   \mathbb E\Big[\sum_i p_i(v)\Big] \;=\; \sum_{v \in \mathrm{supp}(D)} f(v) \sum_{i=1}^n p_i(v).
--   $$
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_jointPMF
import Definitions.Def_DSICCompComp_Supplement_LPSolution

namespace DSICCompComp

namespace Supplement

/-- The objective of the DSIC revenue LP of Appendix C, the expected revenue
`E[∑_i p_i(v)] = ∑_{v ∈ supp(D)} f(v) · ∑_i p_i(v)` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)). -/
def lpRevenue {n m : ℕ} (E : FiniteSetting n m) (sol : LPSolution E) : ℝ :=
  ∑ v : (i : Fin n) → E.S i, jointPMF E v * ∑ i, sol.p (fun k => some (v k)) i

end Supplement

end DSICCompComp


