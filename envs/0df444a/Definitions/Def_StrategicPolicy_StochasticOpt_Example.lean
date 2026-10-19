-- Prove2me | Definitions.Def_StrategicPolicy_StochasticOpt_Example
-- name    : StrategicPolicy_StochasticOpt_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:49.200606+00:00
-- url     : https://prove2.me/theorems/ad1a1ce2-2343-4dba-9e48-03988eb4a3c1
-- title:
--   §3, p. 5 — the three-value instance: γ = 0.1, P(x), P(y = 1 | x) and the cost matrix
-- statement:
--   The instance of §3 has three feature values $x\in\{1,2,3\}$, indexed in Lean by $0,1,2$. Its data are $\gamma=0.1$,
--   $$
--   P(x)=(0.1,\,0.4,\,0.5),\qquad P(y=1\mid x)=(1.0,\,0.7,\,0.4),\qquad
--   c(x_i,x_j)=\begin{pmatrix}0&0&0\\0.3&0&0\\1.2&0.3&0\end{pmatrix},
--   $$
--   where row $i$ is the origin $x_i$ and column $j$ the destination $x_j$. Moving down to a lower outcome is free, moving from $x=2$ or from $x=3$ up by one step costs $0.3$, and moving from $x=3$ to $x=1$ costs $1.2$.
--
--   All statements of the mission are about this instance.
--
--   **Formalization Note** The numbers are exact rationals: $1/10$, $(1/10,2/5,1/2)$, $(1,7/10,2/5)$ and $3/10$, $6/5$.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, example after (8)

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting

namespace StrategicPolicy.StochasticOpt

/-- `γ = 0.1` (§3, p. 5). -/
noncomputable def γ0 : ℝ := 1 / 10

/-- `P(x) = (0.1, 0.4, 0.5)` for `x = 1, 2, 3`, i.e. indices `0, 1, 2`. -/
noncomputable def p0 : Fin 3 → ℝ := ![1 / 10, 2 / 5, 1 / 2]

/-- `P(y = 1 | x) = (1.0, 0.7, 0.4)` for `x = 1, 2, 3`. -/
noncomputable def q0 : Fin 3 → ℝ := ![1, 7 / 10, 2 / 5]

/-- The cost matrix of p. 5: row `i` is the origin `x_i`, column `j` the destination `x_j`. -/
noncomputable def c0 : Fin 3 → Fin 3 → ℝ :=
  ![![0, 0, 0], ![3 / 10, 0, 0], ![6 / 5, 3 / 10, 0]]

end StrategicPolicy.StochasticOpt


