-- Prove2me | Definitions.Def_MissionAbort_expectedCost
-- name    : MissionAbort_expectedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:50.675639+00:00
-- url     : https://prove2.me/theorems/c79f90ab-173c-4781-aea4-a13fc7e70969
-- title:
--   The objective of (1) and (7)
-- statement:
--   The expected cost $\mathbb E\big[C(X(\mathfrak T+w_{\mathfrak T/\delta}),\mathfrak T)\big]$ of the rules $a$, for a state process, signals and law. The original problem and the surrogate problem are this objective for the two systems.
--
--   **Formalization Note** The integrand takes finitely many values, and it is measurable for every system of this mission, so it is integrable.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, (1), p.11, and (7), p.15

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_stopIdx
import Definitions.Def_MissionAbort_cost
import Definitions.Def_MissionAbort_realizedCost

namespace MissionAbort

open MeasureTheory

/-- The objective `E[C(X(𝔗 + w_{𝔗/δ}), 𝔗)]` of (1) and of (7) (Sun, Hu & Ye, arXiv:2505.03225v1,
pp.11, 15), for a state process `S`, signals `Y` and law `μ`.

**Formalization Note.** The integrand takes finitely many values, so it is integrable once it is
measurable; `IsSignalSystem`, `IsOriginalSystem` and `IsSurrogateSystem` provide this. -/
noncomputable def expectedCost {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1)) (a : Rule K) : ℝ :=
  ∫ ω, realizedCost M S Y a ω ∂μ

end MissionAbort


