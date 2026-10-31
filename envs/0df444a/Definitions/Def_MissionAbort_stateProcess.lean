-- Prove2me | Definitions.Def_MissionAbort_stateProcess
-- name    : MissionAbort_stateProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:45.850911+00:00
-- url     : https://prove2.me/theorems/670925c4-a9b1-4ee3-935c-dd10243853f9
-- title:
--   The failure process $X(t)$
-- statement:
--   The failure process of the original system: $X(t)(\omega)=\mathrm{state}(T(\omega);t)$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.1, p.9

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_state

namespace MissionAbort

/-- The failure process `X(t)` of the original system as a function of the transition times
(Sun, Hu & Ye, arXiv:2505.03225v1, §3.1, p.9). -/
noncomputable def stateProcess {Ω : Type*} (T : Ω → ℝ × ℝ × ℝ) (t : ℝ) (ω : Ω) : Cluster :=
  state (T ω) t

end MissionAbort


