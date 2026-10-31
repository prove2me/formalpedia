-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_system87Rhs
-- name    : CombOpt_MatroidIntersectionPolytope_system87Rhs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:30.544657+00:00
-- url     : https://prove2.me/theorems/29d823a9-d1a0-4081-a012-0939136f1a31
-- title:
--   Right-hand side of (8.7) as a system $Ax\le b$
-- statement:
--   The right-hand side of (8.7) in the row indexing of its constraint matrix: $r_1(A)$ on row $(1,A)$, $r_2(A)$ on row $(2,A)$, and $0$ on the nonnegativity row of each $e\in S$. It is integral, since ranks are integers.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank

namespace CombOpt.MatroidIntersectionPolytope

/-- **The right-hand side of (8.7)**, written as a system `Ax ≤ b` with the rows of
`system87Matrix`: `r₁(A)` on row `inl (inl A)`, `r₂(A)` on row `inl (inr A)`, and `0` on the
nonnegativity row `inr e`.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305). -/
noncomputable def system87Rhs {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) :
    (Finset S ⊕ Finset S) ⊕ S → ℚ :=
  fun i =>
    match i with
    | Sum.inl (Sum.inl A) => (rank M₁ A : ℚ)
    | Sum.inl (Sum.inr A) => (rank M₂ A : ℚ)
    | Sum.inr _ => 0

end CombOpt.MatroidIntersectionPolytope


