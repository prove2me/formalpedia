-- Prove2me | Definitions.Def_MissionAbort_decisionGrid
-- name    : MissionAbort_decisionGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:45.09409+00:00
-- url     : https://prove2.me/theorems/719b9503-aeef-484a-865f-a31a7b226bb0
-- title:
--   The decision grid
-- statement:
--   The finite set of times read by the abort problem:
--   $$
--   \{n\delta,\ n\delta+w_n : n=0,\dots,N\}.
--   $$
--   It contains $0$. Signals depend on the state at $n\delta$, and the cost depends on the state at $n\delta+w_n$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.3, p.10, and (1), p.11

import Mathlib
import Definitions.Def_MissionAbort_Model

namespace MissionAbort

/-- The finite set of times the mission reads the failure process at (Sun, Hu & Ye,
arXiv:2505.03225v1, §3.3, p.10 and (1), p.11): the sampling epochs `nδ` and the times `nδ + wₙ` at
which the system is stopped, for `n = 0, …, N`. It contains `0`. -/
def decisionGrid {K : ℕ} (M : Model K) : Set ℝ :=
  {t | ∃ n : ℕ, n ≤ M.N ∧ (t = n * M.δ ∨ t = n * M.δ + M.w n)}

end MissionAbort


