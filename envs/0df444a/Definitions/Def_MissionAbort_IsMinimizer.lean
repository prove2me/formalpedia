-- Prove2me | Definitions.Def_MissionAbort_IsMinimizer
-- name    : MissionAbort_IsMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:55.5859+00:00
-- url     : https://prove2.me/theorems/49742ba9-1a93-4afe-ad92-ab3c4d1b8554
-- title:
--   Solutions of (1) and (7)
-- statement:
--   A rule family solves the abort problem for a system if it is admissible and has the smallest expected cost among admissible rule families. For the original system this is Problem (1), for the surrogate Problem (7).
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, (1), p.11, and (7), p.15

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_IsAdmissible
import Definitions.Def_MissionAbort_stopIdx
import Definitions.Def_MissionAbort_cost
import Definitions.Def_MissionAbort_realizedCost
import Definitions.Def_MissionAbort_expectedCost

namespace MissionAbort

open MeasureTheory

/-- `a` solves the abort problem for the state process `S`, signals `Y` and law `μ`: Problem (1) for the
original system and Problem (7) for the surrogate (Sun, Hu & Ye, arXiv:2505.03225v1, pp.11, 15). -/
def IsMinimizer {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (a : Rule K) : Prop :=
  IsAdmissible M.N a ∧
    ∀ b : Rule K, IsAdmissible M.N b → expectedCost M μ S Y a ≤ expectedCost M μ S Y b

end MissionAbort


