-- Prove2me | Definitions.Def_MissionAbort_clusterProcess
-- name    : MissionAbort_clusterProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:58.913443+00:00
-- url     : https://prove2.me/theorems/c43331e7-7c5d-45e7-a650-65297a447324
-- title:
--   The cluster process of the surrogate
-- statement:
--   The process $t\mapsto$ cluster of $X^{(\lambda)}(t)$. The surrogate problem has the same cost structure as the original problem, and the chain enters the cost only through this process.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, p.14

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_clusterOf

namespace MissionAbort

/-- The cluster process of the surrogate chain, the object through which `X⁽λ⁾` enters the cost
("the cost structure remain unchanged", Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.14). -/
def clusterProcess {m₁ m₂ : ℕ} {Ω : Type*} (X : ℝ → Ω → Fin (m₁ + m₂ + 1)) (t : ℝ) (ω : Ω) :
    Cluster :=
  clusterOf m₁ m₂ (X t ω)

end MissionAbort


