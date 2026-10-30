-- Prove2me | Definitions.Def_FlexMargin_IsBasicDualSolution
-- name    : FlexMargin_IsBasicDualSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:59.229594+00:00
-- url     : https://prove2.me/theorems/93bb520f-fec6-4c64-a171-12441615912e
-- title:
--   Basic feasible solution of the dual problem (3)
-- statement:
--   A pair $(y,z)$ is a **basic feasible solution** of the dual problem (3) if it is feasible and the constraints of (3) that hold with equality at $(y,z)$ — the arc constraints $y_i+z_j=p_i$ with $(a_j,b_i)\in\mathcal A$, the equalities $y_i=0$ and the equalities $z_j=0$ — contain $n+m$ linearly independent ones. Equivalently, the normal vectors $e_i+e_j$, $e_i$, $e_j$ of the active constraints span $\mathbb R^{n+m}$.
--
--   Basic feasible solutions are the vertices of the dual polyhedron; Lemma 1 describes the values the product prices can take at them.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, Lemma 1, p. 16, and its proof, p. 40

import Mathlib
import Definitions.Def_FlexMargin_IsDualFeasible

namespace FlexMargin

/-- **Basic feasible solution of the dual problem (3).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), Lemma 1, p. 16 ("Suppose (y∗,z∗) is a basic feasible solution to the dual problem (3)"),
and its proof, p. 40: "basic solutions are achieved at the corners of the polyhedron defined by
{yi + zj = pi | (aj,bi) ∈ A}, {yi = 0 | 1 ≤ i ≤ n} and {zj = 0 | 1 ≤ j ≤ m}. From the above
|A| + m + n equations, we arbitrarily choose m + n linearly independent binding constraints that
identify a unique basic solution."

`IsBasicDualSolution p A y z` says that `(y, z)` is feasible for (3) and that the normal vectors
of the constraints of (3) active at `(y, z)` span the whole space `ℝ^{n+m}`, indexed by
`Fin n ⊕ Fin m` (products first, then plants). The normal of an active arc constraint
`y_i + z_j = p_i` is `e_i + e_j`, that of an active `y_i = 0` is `e_i`, that of `z_j = 0` is `e_j`.

**Formalization Note.** "The active constraints span `ℝ^{n+m}`" is equivalent to the page's
"m + n linearly independent binding constraints" (a spanning family contains a basis); this is
the standard definition of a vertex of the dual polyhedron. -/
def IsBasicDualSolution {m n : ℕ} (p : Fin n → ℝ) (A : Finset (Fin m × Fin n))
    (y : Fin n → ℝ) (z : Fin m → ℝ) : Prop :=
  IsDualFeasible p A y z ∧
    Submodule.span ℝ
      ({v | ∃ a ∈ A, y a.2 + z a.1 = p a.2 ∧
            v = Pi.single (Sum.inl a.2) (1 : ℝ) + Pi.single (Sum.inr a.1) (1 : ℝ)} ∪
        {v | ∃ i, y i = 0 ∧ v = Pi.single (Sum.inl i) (1 : ℝ)} ∪
        {v | ∃ j, z j = 0 ∧ v = Pi.single (Sum.inr j) (1 : ℝ)} :
        Set (Fin n ⊕ Fin m → ℝ)) = ⊤

end FlexMargin


