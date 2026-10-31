-- Prove2me | Definitions.Def_MissionAbort_realizedCost
-- name    : MissionAbort_realizedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:47.437875+00:00
-- url     : https://prove2.me/theorems/5304c482-db4d-4d37-9aa3-0b63976fb0fb
-- title:
--   The realized cost
-- statement:
--   The realized cost of the rules $a$ on the outcome $\omega$, with stopping time $\mathfrak T$: $C\big(X(\mathfrak T+w_{\mathfrak T/\delta}),\mathfrak T\big)$, for a state process $X$ and signals $Y$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, p.11

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_stopIdx
import Definitions.Def_MissionAbort_cost

namespace MissionAbort

/-- The realized cost `C(X(𝔗 + w_{𝔗/δ}), 𝔗)` of the rules `a` on the outcome `ω` (Sun, Hu & Ye,
arXiv:2505.03225v1, §4, p.11), for a state process `S` and signals `Y`. -/
noncomputable def realizedCost {K : ℕ} (M : Model K) {Ω : Type*} (S : ℝ → Ω → Cluster)
    (Y : ℕ → Ω → Fin (K + 1)) (a : Rule K) (ω : Ω) : ℝ :=
  let n := stopIdx M.N a (fun j => Y j ω)
  cost M (S (n * M.δ + M.w n) ω) n

end MissionAbort


