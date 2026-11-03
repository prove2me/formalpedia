-- Prove2me | Definitions.Def_DRAllocCV_IsParetoRobustlyOptimal
-- name    : DRAllocCV_IsParetoRobustlyOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:06.1986+00:00
-- url     : https://prove2.me/theorems/fe9c6f11-36cf-421c-b037-86e198543d29
-- title:
--   Pareto robust optimality (Definition 2)
-- statement:
--   A mechanism $(p,q)$ that is optimal in (MDP) is **Pareto robustly optimal** if no feasible mechanism Pareto robustly dominates it. Such a mechanism attains the optimal worst-case value $z^\star$, and no other feasible mechanism does at least as well under every distribution in $\mathcal P$ and strictly better under one.
--
--   The concept selects among the typically many optimal mechanisms of a distributionally robust problem those that cannot be improved on non-worst-case distributions.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 2

import Mathlib
import Definitions.Def_DRAllocCV_IsOptimal
import Definitions.Def_DRAllocCV_ParetoDominates

open MeasureTheory

namespace DRAllocCV

/-- **Pareto robust optimality** (Definition 2, Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): a mechanism `(p, q)` that is
optimal in (MDP) is Pareto robustly optimal if no feasible mechanism `(p′, q′)` Pareto robustly
dominates it. (A mechanism never Pareto robustly dominates itself, so "no other" and "no"
coincide.) -/
def IsParetoRobustlyOptimal {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi : ι → ℝ)
    (Pset : Set (Measure (ι → ℝ))) (c : ι → ℝ) (p q : ι → (ι → ℝ) → ℝ) : Prop :=
  IsOptimal tlo thi Pset c p q ∧
  ¬ ∃ p' q', ParetoDominates tlo thi Pset c p' q' p q

end DRAllocCV


