-- Prove2me | Definitions.Def_NisanRonen_Rounding_corr
-- name    : NisanRonen_Rounding_corr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:14.939409+00:00
-- url     : https://prove2.me/theorems/ca961213-fa1d-4411-b2c5-8e44cb99f3d6
-- title:
--   Corrected time vector $\mathrm{corr}^i(x, t, \tilde t)$
-- statement:
--   Let $i$ be an agent and $x$ an allocation. Given the agents' declarations $t = (t^l_j)$ and the vector of actual times $\tilde t$, the **corrected time vector** for agent $i$ is
--
--   $$
--   \mathrm{corr}^i(x, t, \tilde t)_j =
--   \begin{cases}
--   \tilde t_j & \text{if } j \in x^i, \\
--   t^l_j & \text{if } j \in x^l \text{ and } l \neq i .
--   \end{cases}
--   $$
--
--   Agent $i$'s own tasks are counted at their actual times and every other task at the time declared by the agent that received it. The bonus of agent $i$ is minus the (rounded) make-span of this vector.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 22, p. 187 (PDF p. 22)

import Mathlib

namespace NisanRonen.Rounding

/-- **Corrected time vector** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 22, p. 187): for an agent `i`, an
allocation `x`, declarations `d` and actual times `t̃`,
`corr^i(x, d, t̃)_j = t̃_j` if `j ∈ x^i`, and `= d^l_j` if `j ∈ x^l` with `l ≠ i`.
So agent `i`'s own tasks are counted at their actual times and every other task at the time
declared by the agent it is allocated to. -/
def corr {n k : ℕ} (i : Fin n) (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ)
    (tt : Fin k → ℝ) : Fin k → ℝ :=
  fun j => if x j = i then tt j else d (x j) j

end NisanRonen.Rounding


