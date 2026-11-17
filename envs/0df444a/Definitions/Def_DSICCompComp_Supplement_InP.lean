-- Prove2me | Definitions.Def_DSICCompComp_Supplement_InP
-- name    : DSICCompComp_Supplement_InP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:26:11.899247+00:00
-- url     : https://prove2.me/theorems/4ff00e47-92fe-45d7-a530-f5c3e255f253
-- title:
--   The polyhedron $P(D)$
-- statement:
--   $P(D)$ is the set of solutions $(x, p)$ satisfying the constraints of the DSIC revenue LP other than the DSIC constraints:
--
--   1. $\sum_i x_{ij}(v) \le 1$ for all items $j$ and $v \in \mathrm{supp}(D)$;
--   2. $x_{ij}(v) \ge 0$ for all $i$, $j$ and $v \in \mathrm{supp}(D)$;
--   3. $x_{ij}(\varnothing, v_{-i}) = 0$ for all $i$, $j$ and $v_{-i} \in \mathrm{supp}(D_{-i})$;
--   4. $p_i(\varnothing, v_{-i}) = 0$ for all $i$ and $v_{-i} \in \mathrm{supp}(D_{-i})$.
--
--   Payments are unconstrained in sign. $P(D)$ is the domain over which the partial Lagrangian is maximized.
--
--   **Formalization Note** $v_{-i}$ is read off a full profile $v \in \mathrm{supp}(D)$ whose $i$-th entry is overwritten; each $\mathrm{supp}(D_i)$ is nonempty because $f_i$ sums to $1$, so this ranges over exactly $\mathrm{supp}(D_{-i})$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_LPSolution
import Definitions.Def_DSICCompComp_Supplement_devProfile

namespace DSICCompComp

namespace Supplement

/-- Membership in the polyhedron `P(D)` of Appendix C (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)): the constraints of the DSIC revenue LP other than the DSIC
constraints, namely
1. `∑_i x_ij(v) ≤ 1` for all items `j` and `v ∈ supp(D)`;
2. `x_ij(v) ≥ 0` for all `i`, `j` and `v ∈ supp(D)`;
3. `x_ij(∅, v_{-i}) = 0` for all `i`, `j` and `v_{-i} ∈ supp(D_{-i})`;
4. `p_i(∅, v_{-i}) = 0` for all `i` and `v_{-i} ∈ supp(D_{-i})`.

**Formalization Note** `v_{-i}` is read off a full profile `v` (its `i`-th entry is overwritten by
`devProfile`); every `supp(D_i)` is nonempty since `f_i` sums to `1`, so this ranges over exactly
`supp(D_{-i})`. Payments are unconstrained in sign. -/
def InP {n m : ℕ} (E : FiniteSetting n m) (sol : LPSolution E) : Prop :=
  (∀ (v : (i : Fin n) → E.S i) (j : Fin m), ∑ i, sol.x (fun k => some (v k)) i j ≤ 1) ∧
  (∀ (v : (i : Fin n) → E.S i) (i : Fin n) (j : Fin m), 0 ≤ sol.x (fun k => some (v k)) i j) ∧
  (∀ (v : (i : Fin n) → E.S i) (i : Fin n) (j : Fin m), sol.x (devProfile E v i none) i j = 0) ∧
  (∀ (v : (i : Fin n) → E.S i) (i : Fin n), sol.p (devProfile E v i none) i = 0)

end Supplement

end DSICCompComp


