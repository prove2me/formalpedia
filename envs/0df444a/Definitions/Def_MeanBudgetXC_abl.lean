-- Prove2me | Definitions.Def_MeanBudgetXC_abl
-- name    : MeanBudgetXC_abl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:40.678058+00:00
-- url     : https://prove2.me/theorems/3ab84e9c-c155-40ae-b5b9-78ad80566112
-- title:
--   The antiblocker $\mathrm{abl}(A)$
-- statement:
--   The **antiblocker** of a set $A$ in $\mathbb{R}^\iota$ is
--   $$\mathrm{abl}(A)=\{y\ge0:y\cdot x\le1\text{ for every }x\in A\}.$$
--   For polyhedra this is the classical construction of Fulkerson.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4, p.17, and Appendix A.1, p.37

import Mathlib

namespace MeanBudgetXC

open Matrix

variable {ι : Type*} [Fintype ι]

/-- The **antiblocker** `abl(A) = {y ≥ 0 : y · x ≤ 1 for every x ∈ A}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4, p.17, and
Appendix A.1, p.37). -/
def abl (A : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {y | 0 ≤ y ∧ ∀ x ∈ A, y ⬝ᵥ x ≤ 1}

end MeanBudgetXC


