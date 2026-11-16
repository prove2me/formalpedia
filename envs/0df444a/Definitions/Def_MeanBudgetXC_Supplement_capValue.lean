-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_capValue
-- name    : MeanBudgetXC_Supplement_capValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:07:59.694681+00:00
-- url     : https://prove2.me/theorems/7276a457-3417-4dd0-a76b-1b7b2020aa2b
-- title:
--   The capped value $V_A(u)$
-- statement:
--   For a set $A\subseteq\mathbb R^\iota$ and a cap $u$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\},$$
--   the largest total mass of a point of $A$ below the cap.
--
--   **Formalization Note** The value is defined as the supremum of $\sum_eq_e$ over the capped set. That set lies in the box $[0,u]$, so the supremum is finite; when it is nonempty and $A$ is a polyhedron or a compact body (every use here) it is attained and equals the maximum. On an empty capped set the supremum is $0$ by Lean's convention; every statement assumes nonemptiness for the surrogate $K$, and the target bodies contain $0$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 1.3, p.5

import Mathlib
import Definitions.Def_MeanBudgetXC_Supplement_cappedSet

namespace MeanBudgetXC.Supplement

/-- The **capped value** `V_A(u) = max{1ᵀq : q ∈ A, 0 ≤ q ≤ u}` of a set `A ⊆ ℝ^ι` at the cap `u`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.3, p.5).

**Formalization Note** The value is the supremum of the total mass `∑_e q_e` over the capped set
`cappedSet A u`. That set lies in the box `[0, u]`, so the supremum is always finite; when the
capped set is nonempty and `A` is a polyhedron or a compact set (every use in this mission), the
supremum is attained and equals the paper's maximum. On an empty capped set the value is
`sSup ∅ = 0`; every statement that applies `capValue` to a surrogate `K` assumes the capped set
nonempty, as the paper does ("Each prescribed query must have a nonempty feasible set and finite
value", p.5), and the target bodies contain `0`. -/
noncomputable def capValue {ι : Type*} [Fintype ι] (A : Set (ι → ℝ)) (u : ι → ℝ) : ℝ :=
  sSup ((fun q : ι → ℝ => ∑ e, q e) '' cappedSet A u)

end MeanBudgetXC.Supplement


