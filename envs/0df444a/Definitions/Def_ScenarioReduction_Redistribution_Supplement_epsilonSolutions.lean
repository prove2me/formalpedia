-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_Supplement_epsilonSolutions
-- name    : ScenarioReduction_Redistribution_Supplement_epsilonSolutions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:27:13.568995+00:00
-- url     : https://prove2.me/theorems/d285e654-b339-466c-8cce-f0988b6a5e13
-- title:
--   Global epsilon-solution sets
-- statement:
--   For the stochastic program with feasible set $X$, random integrand $f$ and probability law $Q$, write $F_Q(x)=E_Q f(\omega,x)$ and $v(Q)=\inf_{x\in X}F_Q(x)$. For $\varepsilon\ge0$, define
--
--   $$S_\varepsilon(Q)=\{x\in X:F_Q(x)\le v(Q)+\varepsilon\}.$$
--
--   These are global approximate minimizers, with $S(Q)=S_0(Q)$. They are not restricted to a neighborhood or a selected ball.
--
--   **Formalization Note** The global value and exact minimizers are the referenced model's `M.v` and `M.S`, specialized to zero stochastic constraints. The latter uses equality with the infimum, equivalent to the displayed zero sublevel condition. Values and expectations remain extended real; no real conversion is used. The definition is total for real epsilon, while all theorem uses have epsilon positive.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 494, unnumbered definitions of v, S and S_epsilon, PDF 2

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
set_option autoImplicit false

namespace ScenarioReduction.Redistribution.Supplement

/-- The global epsilon-solution sets, p. 494. For d = 0 the imported M.v is
exactly the infimum over X and M.S is the corresponding global minimizer set. -/
def epsilonSolutions {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (Q : MeasureTheory.Measure M.Ξ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ M.X ∧ M.integral Q 0 x ≤ M.v Q + (ε : EReal)}

end ScenarioReduction.Redistribution.Supplement


