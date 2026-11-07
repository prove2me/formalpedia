-- Prove2me | Definitions.Def_MeanBudgetXC_downClosure
-- name    : MeanBudgetXC_downClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:34.280276+00:00
-- url     : https://prove2.me/theorems/bb1c44fc-957e-4282-a462-4edc2c3876cf
-- title:
--   Downward closure $\downarrow A$
-- statement:
--   The **downward closure** of a set $A$ in $\mathbb{R}^\iota$ is
--   $$\downarrow A=\{x\ge0:\exists a\in A,\ x\le a\},$$
--   with the componentwise order. A set is **down-closed** when it equals its downward closure.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4, p.17, and Appendix A.1, p.37

import Mathlib

namespace MeanBudgetXC

variable {ι : Type*} [Fintype ι]

/-- The **downward closure** `↓A = {x ≥ 0 : ∃ a ∈ A, x ≤ a}` of a set `A ⊆ ℝ^ι`
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4, p.17, and Appendix A.1, p.37). A set is
down-closed when it equals its downward closure. The orders are componentwise. -/
def downClosure (A : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | 0 ≤ x ∧ ∃ a ∈ A, x ≤ a}

end MeanBudgetXC


