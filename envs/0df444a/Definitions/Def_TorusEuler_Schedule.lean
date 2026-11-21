-- Prove2me | Definitions.Def_TorusEuler_Schedule
-- name    : TorusEuler_Schedule
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T19:37:13.341272+00:00
-- url     : https://prove2.me/theorems/0db62a86-7d3e-45e9-88ee-2d5c1ad49413
-- title:
--   Frequency exponent $K(s) = 320b(s+1)$ of the frozen schedule
-- statement:
--   The frequency exponent of the construction's schedule: for an integer parameter $b\ge1$ and an order $s$,
--   $$K(s) = 320\,b\,(s+1).$$
--   In the frozen schedule (1.14), successive frequencies satisfy $\lambda_j = \lambda_{j-1}^{K(q_j)}$, where $q_j$ is the spatial derivative order reached at step $j$. The exponent separates successive frequencies and controls the logarithmic gains $L_j = 4\log\lambda_{j+1}$.
--
--   **Formalization Note** In the paper $K$ is applied to positive orders; the Lean definition is total on $\mathbb{N}$ and agrees with $320b(s+1)$ everywhere.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/FrequencySchedule.lean#L7; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/01b_parameters.tex (schedule cc:uf:tower:eq:schedule).

import Mathlib

namespace TorusEuler

/-- The frequency exponent in (1.14). It is applied to positive orders in the paper. -/
def frequencyExponent (b s : ℕ) : ℕ :=
  320 * b * (s + 1)

end TorusEuler


