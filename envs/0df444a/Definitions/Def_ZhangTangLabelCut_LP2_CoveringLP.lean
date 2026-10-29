-- Prove2me | Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
-- name    : ZhangTangLabelCut_LP2_CoveringLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:11:22.981981+00:00
-- url     : https://prove2.me/theorems/a4404165-6f3d-4ab2-8092-24d715a13498
-- title:
--   Finite nonnegative covering linear programs
-- statement:
--   For a finite variable set $L$, a covering linear program consists of a finite family $\mathcal R$ of subsets of $L$, a real cost $c_\ell$ for each variable, and a real right-hand side $b_R$ for each row. Its feasible vectors and objective are
--   $$x\in\mathbb R^L,\qquad x_\ell\ge0,\qquad \sum_{\ell\in R}x_\ell\ge b_R\ (R\in\mathcal R),\qquad c^Tx=\sum_{\ell\in L}c_\ell x_\ell.$$
--   Its value is the extended-real infimum of feasible objective values, with $+\infty$ for infeasibility and $-\infty$ for unboundedness below. This reusable covering-program object adds no boundedness or attainment hypotheses and no variable upper bounds.
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 7, LP2, reusable covering-program abstraction

import Mathlib

namespace ZhangTangLabelCut.LP2

/-- A finite nonnegative covering LP, with real variables and arbitrary covering rows. -/
structure CoveringLP (L : Type) [Fintype L] where
  rows : Finset (Finset L)
  cost : L → ℝ
  rhs : Finset L → ℝ

noncomputable def CoveringLP.Feasible {L : Type} [Fintype L]
    (P : CoveringLP L) (x : L → ℝ) : Prop :=
  (∀ l, 0 ≤ x l) ∧ ∀ R ∈ P.rows, P.rhs R ≤ ∑ l ∈ R, x l

noncomputable def CoveringLP.objective {L : Type} [Fintype L]
    (P : CoveringLP L) (x : L → ℝ) : ℝ := ∑ l, P.cost l * x l

/-- The extended-real optimum: +∞ on an infeasible LP, -∞ if unbounded below. -/
noncomputable def CoveringLP.value {L : Type} [Fintype L] (P : CoveringLP L) : EReal :=
  sInf {v | ∃ x, P.Feasible x ∧ v = (P.objective x : EReal)}

end ZhangTangLabelCut.LP2


