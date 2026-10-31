-- Prove2me | Definitions.Def_MissionAbort_costAbort
-- name    : MissionAbort_costAbort
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:27.346522+00:00
-- url     : https://prove2.me/theorems/1e9d01b6-23a6-487f-8600-38688684f7e4
-- title:
--   The abort cost-to-go $\mathbb C_{ab}$
-- statement:
--   The cost-to-go of aborting at time $n\delta$ given $Y_{1:n}=y$:
--   $$
--   \mathbb C_{ab}(n,y)=C_m+C_s\,\mathbb P(\xi\le n\delta+w_n\mid Y_{1:n}=y).
--   $$
--   The event $\{\xi\le t\}$ is the event that the state is failed at $t$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.3; (11), p.17

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_histEvent
import Definitions.Def_MissionAbort_condProb

namespace MissionAbort

open MeasureTheory

/-- The cost-to-go of aborting at time `nδ` given `Y_{1:n} = y` (Sun, Hu & Ye, arXiv:2505.03225v1,
Appendix A.2, p.EC.3; (11), p.17): `Cab(n, y) = Cm + Cs P(ξ ≤ nδ + wₙ | Y_{1:n} = y)`. The event
`{ξ ≤ t}` is `{S(t) = failed}`. -/
noncomputable def costAbort {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ) (y : Fin n → Fin (K + 1)) : ℝ :=
  M.Cm + M.Cs * condProb μ {ω | S (n * M.δ + M.w n) ω = .failed} (histEvent Y n y)

end MissionAbort


