-- Prove2me | Definitions.Def_AcceptSubcube_Supplement_Lstar
-- name    : AcceptSubcube_Supplement_Lstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:49:33.605267+00:00
-- url     : https://prove2.me/theorems/97d67376-f82f-4d1e-8ac0-234c6a880ad3
-- title:
--   The budgeted Hamming-ball LP value $L^*_{\tau,r}$
-- statement:
--   For an instance $\mathcal I$ of arity $k$, a center $\tau\in\{0,1\}^n$ and a radius $r$, the **budgeted Hamming-ball LP value** is
--   $$L^*_{\tau,r}=\inf\Big\{\sum_E\Pr_\mu[P_E(x_E)=0]\Big\},$$
--   the infimum over the points $\mu$ of the relaxation of §4.3 after XORing every coordinate with $\tau$: locally consistent, normalized distributions $\mu_T$ on $\{0,1\}^T$ for all $|T|\le k$, subject to the conditional budgets (10)
--   $$\sum_{j=1}^n\Pr[x_S=a,\;x_j=1]\le r\,\Pr[x_S=a]\qquad(|S|\le2,\ a\in\{0,1\}^S).$$
--   There is no semidefinite constraint.
--
--   This is the quantity whose integrality gap Theorem 4.11 bounds from below.
--
--   **Formalization Note** Points are the rational moment lists of the published `RelaxFeasible` (the moment parametrization makes the local laws normalized and consistent), and the objective is the published `relaxObj` of the shifted instance `shift I τ`. The feasible set is nonempty (the point mass at the center) and the objective is nonnegative on well-formed instances, so the infimum is the LP's value; the LP has rational data, so its optimum is attained at a rational point.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §4.3, p.17 (relaxation (10)); Theorem 4.11, p.23

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_RelaxFeasible

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **The budgeted Hamming-ball LP value** `L*_{τ,r}` of §4.3: the infimum of the objective
`L = Σ_E P[P_E(x_E) = 0]` over the relaxation of §4.3 (local laws on every set of at most `k`
variables, normalized and consistent, and the conditional budgets (10)), after shifting the center
`τ` to `0^n`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §4.3, p.17 (the relaxation (10)); Theorem 4.11,
p.23: "the budgeted Hamming-ball LP value L*_{τ,r} of Section 4.3".

**Formalization Note.** The points are the rational moment lists of the published `RelaxFeasible`
and the objective is the published `relaxObj` of the shifted instance (`shift`). No semidefinite
constraint (14). The feasible set is nonempty (the point mass at `0^n`, i.e. the empty moment list,
in which every nonempty moment is `0`), and for a well-formed `k`-uniform instance the objective is a
sum of local probabilities of nonnegative laws, so the infimum is the paper's minimum value and not
a junk value; the LP has rational data, so its optimum is attained at a rational point and the
restriction to rational moment lists loses nothing. -/
noncomputable def Lstar (k : ℕ) (I : GInst) (τ : Fin I.n → Bool) (r : ℕ) : ℝ :=
  sInf ((fun L => ((relaxObj (shift I τ) L : ℚ) : ℝ)) '' {L | RelaxFeasible k I.n r L})

end AcceptSubcube.Supplement


