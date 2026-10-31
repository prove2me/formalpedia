-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_matroidLP
-- name    : CombOpt_MatroidIntersectionPolytope_matroidLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:23.60805+00:00
-- url     : https://prove2.me/theorems/85636adc-7376-48fd-b428-fff7fe430eb5
-- title:
--   Feasible set of the matroid linear program (8.1)
-- statement:
--   For a matroid $M$ on $S$ with rank function $r$, the linear program (8.1) is: maximize $\sum_{e\in S}c_ex_e$ subject to
--
--   $$
--   x(A)\le r(A)\ \text{ for all } A\subseteq S,\qquad x_e\ge0\ \text{ for all } e\in S,
--   $$
--
--   where $x(A)=\sum_{e\in A}x_e$. This definition is the set of $x\in\mathbb R^S$ satisfying these constraints. The characteristic vector of every independent set lies in it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.1), p. 278 (PDF p. 285)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank

namespace CombOpt.MatroidIntersectionPolytope

/-- **Feasible set of the matroid linear program (8.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, (8.1), p. 278 (PDF p. 285): "Maximize Σ(c_e x_e : e ∈ S) subject to
x(A) ≤ r(A), for all A ⊆ S; x_e ≥ 0, for all e ∈ S."

`matroidLP M` is the set of `x ∈ ℝ^S` with `x(A) = Σ_{e∈A} x_e ≤ r(A)` for every `A ⊆ S` and
`x ≥ 0`. -/
def matroidLP {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S) : Set (S → ℝ) :=
  {x | (∀ A : Finset S, ∑ e ∈ A, x e ≤ (rank M A : ℝ)) ∧ ∀ e, 0 ≤ x e}

end CombOpt.MatroidIntersectionPolytope


