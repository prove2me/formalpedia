-- Prove2me | Definitions.Def_DSICCompComp_Supplement_dsicSlack
-- name    : DSICCompComp_Supplement_dsicSlack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:25:26.916599+00:00
-- url     : https://prove2.me/theorems/7076b255-44bb-48ab-b4b8-5a7514318d12
-- title:
--   Slack of the DSIC constraint for $(i, v, v'_i)$
-- statement:
--   For a candidate solution $(x, p)$, a bidder $i$, a value profile $v \in \mathrm{supp}(D)$ and a report $v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}$, the slack of the corresponding DSIC constraint is
--
--   $$
--   \Big(\sum_{j} x_{ij}(v)\, v_{ij} - p_i(v)\Big) - \Big(\sum_{j} x_{ij}(v'_i, v_{-i})\, v_{ij} - p_i(v'_i, v_{-i})\Big)
--   \;=\; \sum_j v_{ij}\big(x_{ij}(v) - x_{ij}(v'_i, v_{-i})\big) - \big(p_i(v) - p_i(v'_i, v_{-i})\big).
--   $$
--
--   The DSIC constraint asks that it be nonnegative, and the constraint **binds** when it is zero. With $v'_i = \varnothing$ this is the individual rationality constraint. The same expression multiplies the dual variable $\lambda^{v_{-i}}_i(v_i, v'_i)$ in the partial Lagrangian.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_LPSolution
import Definitions.Def_DSICCompComp_Supplement_devProfile

namespace DSICCompComp

namespace Supplement

/-- The slack of the DSIC constraint of Appendix C for bidder `i`, true profile `v ∈ supp(D)` and
report `v'_i ∈ supp(D_i) ∪ {∅}` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)):
`(∑_j x_ij(v)·v_ij − p_i(v)) − (∑_j x_ij(v'_i, v_{-i})·v_ij − p_i(v'_i, v_{-i}))`.
The DSIC constraint is `slack ≥ 0`; it binds when `slack = 0`. The same expression,
`∑_j v_ij·(x_ij(v) − x_ij(v'_i, v_{-i})) − (p_i(v) − p_i(v'_i, v_{-i}))`, multiplies `λ^{v_{-i}}_i(v_i, v'_i)`
in the partial Lagrangian.

**Formalization Note** `w = none` is the report `∅` (the IR constraint). -/
def dsicSlack {n m : ℕ} (E : FiniteSetting n m) (sol : LPSolution E) (v : (i : Fin n) → E.S i)
    (i : Fin n) (w : Option (E.S i)) : ℝ :=
  (∑ j, sol.x (fun k => some (v k)) i j * (v i : Fin m → ℝ) j - sol.p (fun k => some (v k)) i) -
    (∑ j, sol.x (devProfile E v i w) i j * (v i : Fin m → ℝ) j - sol.p (devProfile E v i w) i)

end Supplement

end DSICCompComp


