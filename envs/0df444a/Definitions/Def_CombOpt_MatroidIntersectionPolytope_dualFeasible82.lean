-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_dualFeasible82
-- name    : CombOpt_MatroidIntersectionPolytope_dualFeasible82
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:34.971114+00:00
-- url     : https://prove2.me/theorems/af95de72-8e48-421a-8288-80b1e7963f56
-- title:
--   Feasible set of the dual matroid program (8.2)
-- statement:
--   The dual of (8.1) is (8.2): minimize $\sum_{A\subseteq S}r(A)y_A$ subject to
--
--   $$
--   \sum(y_A : e\in A\subseteq S)\ge c_e\ \text{ for all } e\in S,\qquad y_A\ge0\ \text{ for all } A\subseteq S.
--   $$
--
--   This definition is the set of feasible $y\in\mathbb R^{2^S}$; it depends only on $c$, while the objective involves the matroid.
--
--   **Formalization Note** The printed constraint says "for all $e\in E$"; the ground set in this chapter is $S$, so it is read as "for all $e\in S$".
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_coverSum

namespace CombOpt.MatroidIntersectionPolytope

/-- **Feasible set of the dual matroid linear program (8.2).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286): "Minimize Σ(r(A) y_A : A ⊆ S) subject to
Σ(y_A : e ∈ A ⊆ S) ≥ c_e, for all e ∈ E; y_A ≥ 0, for all A ⊆ S."

`dualFeasible82 c` is the set of `y : 2^S → ℝ` with `y ≥ 0` and `Σ_{A ∋ e} y_A ≥ c_e` for every
`e ∈ S`. (The constraints do not involve the matroid; only the objective does.)

**Formalization Note.** The printed constraint reads "for all e ∈ E"; in this chapter the ground
set is `S`, so it is read as "for all e ∈ S". -/
def dualFeasible82 {S : Type*} [Fintype S] [DecidableEq S] (c : S → ℝ) :
    Set (Finset S → ℝ) :=
  {y | (∀ A, 0 ≤ y A) ∧ ∀ e, c e ≤ coverSum y e}

end CombOpt.MatroidIntersectionPolytope


