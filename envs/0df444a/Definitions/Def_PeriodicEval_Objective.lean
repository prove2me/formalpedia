-- Prove2me | Definitions.Def_PeriodicEval_Objective
-- name    : PeriodicEval_Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:44.113011+00:00
-- url     : https://prove2.me/theorems/ed54b116-e10c-4ab0-8eae-776134730d41
-- title:
--   Objective and value function $V(x)$ of problem (4)
-- statement:
--   For a portfolio value process $X$, the objective of problem (4) is the expected discounted sum of the periodic utilities of performance,
--
--   $$J(X):=E\Big[\sum_{i=1}^\infty e^{-\beta T_i}\,U\big(X_{T_i}-\gamma X_{T_{i-1}}\big)\Big],$$
--
--   and the **value function** is
--
--   $$V(x):=\sup_{X\in\mathcal A_0(x)}J(X),\qquad x>0.$$
--
--   The agent derives utility from the performance $X_{T_i}-\gamma X_{T_{i-1}}$ of each period $(T_{i-1},T_i]$ relative to the target $\gamma$, discounted at rate $\beta$.
--
--   **Formalization Note** The sum over $i=1,2,\dots$ is written with index $i+1$, $i\in\mathbb N$. For every admissible $X$ the positive and negative parts of the series have summable expectations (milestone `objective_summable`), so the sum and the expectation are genuine. $V$ is a supremum in the extended reals.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), eq. (2), p.7 and eq. (4), p.8

import Mathlib
import Definitions.Def_PeriodicEval_Utility
import Definitions.Def_PeriodicEval_Admissible

open MeasureTheory
open scoped NNReal

namespace PeriodicEval

/-- The objective of problem (4), SSRN 3971852 (June 20, 2023), p.8, for a portfolio value
process `X`: `E[∑_{i=1}^∞ e^{−βT_i} U(X_{T_i} − γX_{T_{i−1}})]`.

**Formalization Note** The sum over `i = 1, 2, …` is written over `i : ℕ` with the summand at
`i + 1`. The `tsum` and the Bochner expectation are genuine for every admissible `X`: both the
positive and the negative parts of the series have summable expectations (the claim around
(25), p.42, milestone `objective_summable`). -/
noncomputable def objective (p : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ∑' i : ℕ, Real.exp (-(p.β * (p.T (i + 1) : ℝ))) *
    U p (X (p.T (i + 1)) ω - p.γ * X (p.T i) ω) ∂P

/-- The value function (4), SSRN 3971852 (June 20, 2023), p.8:
`V(x) := sup_{X ∈ A_0(x)} E[∑_{i=1}^∞ e^{−βT_i} U(X_{T_i} − γX_{T_{i−1}})]`.

**Formalization Note** The supremum is taken in `EReal`, so an unbounded set of objective
values gives `⊤` rather than a junk real value. -/
noncomputable def V (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (x : ℝ) : EReal :=
  sSup {z : EReal | ∃ X ∈ admissible p P ℱ B 0 x, z = ((objective p P X : ℝ) : EReal)}

end PeriodicEval


