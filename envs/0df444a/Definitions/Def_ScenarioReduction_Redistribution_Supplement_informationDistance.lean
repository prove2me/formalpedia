-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_Supplement_informationDistance
-- name    : ScenarioReduction_Redistribution_Supplement_informationDistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:30:01.160651+00:00
-- url     : https://prove2.me/theorems/8c777b63-ad87-4663-b730-e357b1463425
-- title:
--   Minimal information probability distance
-- statement:
--   For admissible probability measures $P,Q$ and $\rho>0$, let $F_P(x)=E_P f(\omega,x)$ and $F_Q(x)=E_Q f(\omega,x)$. The minimal information distance is
--
--   $$d_{f,\rho}(P,Q)=\sup_{x\in X,\ \|x\|\le\rho}|F_P(x)-F_Q(x)|.$$
--
--   It measures differences of expected objectives at every feasible decision in the ball, rather than differences of optimal values or a transportation cost.
--
--   **Formalization Note** The supremum and absolute values take values in the nonnegative extended reals, so unbounded families give positive infinity. An empty supremum is zero. Admissibility makes all expected objectives at feasible decisions finite; the theorem's strict closeness hypotheses also make the distances appearing in its conclusions finite.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 496, Section 2, definition of d_f,rho, PDF 4

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
set_option autoImplicit false
open scoped ENNReal

namespace ScenarioReduction.Redistribution.Supplement

/-- The minimal information distance, p. 496, in the nonnegative extended reals. -/
noncomputable def informationDistance {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (ρ : ℝ) (P Q : MeasureTheory.Measure M.Ξ) : ℝ≥0∞ :=
  ⨆ x ∈ {x : EuclideanSpace ℝ (Fin n) | x ∈ M.X ∧ ‖x‖ ≤ ρ},
    EReal.abs (M.integral P 0 x - M.integral Q 0 x)

end ScenarioReduction.Redistribution.Supplement


