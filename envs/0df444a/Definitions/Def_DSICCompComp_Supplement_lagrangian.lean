-- Prove2me | Definitions.Def_DSICCompComp_Supplement_lagrangian
-- name    : DSICCompComp_Supplement_lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:30:20.325199+00:00
-- url     : https://prove2.me/theorems/dfa10e89-de81-4607-bd70-95d48997c95e
-- title:
--   Partial Lagrangian $L(\lambda, x, p)$
-- statement:
--   Lagrangifying only the DSIC constraints of the revenue LP gives the partial Lagrangian
--
--   $$
--   L(\lambda, x, p) = \sum_{i,\, v \in \mathrm{supp}(D)} f(v)\, p_i(v) \;+\; \sum_{\substack{i,\, v \in \mathrm{supp}(D),\\ v'_i \in \mathrm{supp}(D_i) \cup \{\varnothing\}}} \lambda^{v_{-i}}_i(v_i, v'_i) \Big(\sum_j v_{ij}\big(x_{ij}(v) - x_{ij}(v'_i, v_{-i})\big) - \big(p_i(v) - p_i(v'_i, v_{-i})\big)\Big).
--   $$
--
--   **Formalization Note** The bracket is `dsicSlack`, the same expression. Dual solutions are encoded as in `FlowConservation`.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_jointPMF
import Definitions.Def_DSICCompComp_Supplement_dsicSlack

namespace DSICCompComp

namespace Supplement

/-- The partial Lagrangian `L(λ, x, p)` of the DSIC revenue LP, in which only the DSIC constraints are
Lagrangified (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)):
`L(λ, x, p) = ∑_{i, v ∈ supp(D)} f(v)·p_i(v) + ∑_{i, v ∈ supp(D), v'_i ∈ supp(D_i) ∪ {∅}} λ^{v_{-i}}_i(v_i, v'_i)·(∑_j v_ij·(x_ij(v) − x_ij(v'_i, v_{-i})) − (p_i(v) − p_i(v'_i, v_{-i})))`.

**Formalization Note** The bracket multiplying `λ^{v_{-i}}_i(v_i, v'_i)` is `dsicSlack` (the same
expression); dual solutions are encoded as in `FlowConservation`. -/
def lagrangian {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ) (sol : LPSolution E) : ℝ :=
  ∑ i, ∑ v : (k : Fin n) → E.S k, jointPMF E v * sol.p (fun k => some (v k)) i +
    ∑ i, ∑ v : (k : Fin n) → E.S k, ∑ w : Option (E.S i), lam i v w * dsicSlack E sol v i w

end Supplement

end DSICCompComp


