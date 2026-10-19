-- Prove2me | Definitions.Def_StrategicPolicy_NonMonotone_Example
-- name    : StrategicPolicy_NonMonotone_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:28.541249+00:00
-- url     : https://prove2.me/theorems/10b34218-3822-4bc4-8c5a-581aeaa954cb
-- title:
--   Section 5 three-value general-cost instance
-- statement:
--   The paper's Section 5 example has three feature values $x_1,x_2,x_3$. Its initial distribution, positive-outcome probabilities, decision cost, and feature-change cost matrix are exactly
--
--   $$
--   p=(0.1,0.4,0.5),\qquad q=(1,0.7,0.4),\qquad \gamma=0.1,\qquad
--   c=\begin{pmatrix}0&0.2&0.3\\0.3&0&0.7\\1.2&1.1&0\end{pmatrix}.
--   $$
--
--   Matrix row $i$ is an individual's initial value $x_i$; column $j$ is the destination $x_j$. This fixed instance is used by both milestones and the goal.
--
--   **Formalization Note** `Fin 3` indices $0,1,2$ stand for $x_1,x_2,x_3$, respectively. All decimals are represented as exact rational real numbers.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 9, §5 general-cost example

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting

namespace StrategicPolicy.NonMonotone

/-- Initial feature distribution in the Section 5 three-value example. -/
noncomputable def p : Fin 3 → ℝ := ![1 / 10, 2 / 5, 1 / 2]

/-- Positive-outcome probabilities in the Section 5 three-value example. -/
noncomputable def q : Fin 3 → ℝ := ![1, 7 / 10, 2 / 5]

/-- Cost of moving from row feature to column feature in the Section 5 example. -/
noncomputable def c : Fin 3 → Fin 3 → ℝ := !![0, 1 / 5, 3 / 10; 3 / 10, 0, 7 / 10; 6 / 5, 11 / 10, 0]

/-- The decision maker's cost parameter in the Section 5 example. -/
noncomputable def γ : ℝ := 1 / 10

end StrategicPolicy.NonMonotone


