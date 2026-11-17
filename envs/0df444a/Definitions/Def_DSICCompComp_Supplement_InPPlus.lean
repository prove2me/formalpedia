-- Prove2me | Definitions.Def_DSICCompComp_Supplement_InPPlus
-- name    : DSICCompComp_Supplement_InPPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:27:01.460605+00:00
-- url     : https://prove2.me/theorems/723dbfaf-3007-4b6a-bf25-058dfe43a2fd
-- title:
--   The feasible set $P^+(D)$ of the DSIC revenue LP
-- statement:
--   $P^+(D)$ is the set of feasible solutions of the DSIC revenue LP: the solutions in $P(D)$ that also satisfy every DSIC constraint
--
--   $$
--   \sum_j x_{ij}(v)\, v_{ij} - p_i(v) \;\ge\; \sum_j x_{ij}(v'_i, v_{-i})\, v_{ij} - p_i(v'_i, v_{-i})
--   $$
--
--   for all bidders $i$, values $v_i \in \mathrm{supp}(D_i)$, reports $v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}$ and profiles $v_{-i} \in \mathrm{supp}(D_{-i})$. These are the DSIC/IR mechanisms on the finite support (IR is the case $v'_i = \varnothing$).
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_InP
import Definitions.Def_DSICCompComp_Supplement_dsicSlack

namespace DSICCompComp

namespace Supplement

/-- Membership in `P⁺(D)`, the feasible set of the DSIC revenue LP of Appendix C
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)): `P(D)` together with every DSIC constraint
`∑_j x_ij(v)·v_ij − p_i(v) ≥ ∑_j x_ij(v'_i, v_{-i})·v_ij − p_i(v'_i, v_{-i})` for all `i`,
`v_i ∈ supp(D_i)`, `v'_i ∈ supp(D_i) ∪ {∅}` and `v_{-i} ∈ supp(D_{-i})`, i.e. the DSIC/IR mechanisms
on the finite support. -/
def InPPlus {n m : ℕ} (E : FiniteSetting n m) (sol : LPSolution E) : Prop :=
  InP E sol ∧ ∀ (v : (i : Fin n) → E.S i) (i : Fin n) (w : Option (E.S i)), 0 ≤ dsicSlack E sol v i w

end Supplement

end DSICCompComp


