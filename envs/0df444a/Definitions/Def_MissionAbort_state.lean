-- Prove2me | Definitions.Def_MissionAbort_state
-- name    : MissionAbort_state
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:47.924135+00:00
-- url     : https://prove2.me/theorems/3a3328c2-5dea-461e-8f31-32e9136b690f
-- title:
--   The state function of the failure process
-- statement:
--   For realized transition times $u=(u_{12},u_{13},u_{23})$, the state at time $t$ is
--   $$
--   \mathrm{state}(u;t)=\begin{cases}\text{healthy},& t<\min(u_{12},u_{13}),\\ \text{defective},& u_{12}<u_{13},\ u_{12}\le t<u_{12}+u_{23},\\ \text{failed},& \text{otherwise.}\end{cases}
--   $$
--   So the state is failed at $t$ exactly when $\xi\le t$, where $\xi=u_{13}$ if $u_{13}\le u_{12}$ and $\xi=u_{12}+u_{23}$ otherwise (for $u_{23}\ge 0$).
--
--   The failure process of the original system is this function evaluated at $(T_{12},T_{13},T_{23})$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.1, p.9

import Mathlib
import Definitions.Def_MissionAbort_Cluster

namespace MissionAbort

/-- The state function of the failure process (Sun, Hu & Ye, arXiv:2505.03225v1, §3.1, p.9):
with `u = (u₁₂, u₁₃, u₂₃)` the realized transition times, the system is healthy before
`min(u₁₂, u₁₃)`, defective from `u₁₂` to `u₁₂ + u₂₃` when `u₁₂ < u₁₃`, and failed otherwise. So
`X(t) = 3` iff `ξ ≤ t`, where `ξ = u₁₃` if `u₁₃ ≤ u₁₂` and `ξ = u₁₂ + u₂₃` otherwise.

**Formalization Note.** A tie `u₁₃ = u₁₂` is the failure branch, as in the display for `ξ`, so the
defective branch has the strict `u₁₂ < u₁₃`. -/
noncomputable def state (u : ℝ × ℝ × ℝ) (t : ℝ) : Cluster :=
  if t < min u.1 u.2.1 then .healthy
  else if u.1 < u.2.1 ∧ u.1 ≤ t ∧ t < u.1 + u.2.2 then .defective
  else .failed

end MissionAbort


