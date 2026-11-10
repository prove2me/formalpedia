-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_Streaming
-- name    : CoarseMatching_LowerBound_Streaming
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:01.015005+00:00
-- url     : https://prove2.me/theorems/e7207288-5314-40f9-b186-e42036716968
-- title:
--   Two-sided matching and mixed matching/cover correctness
-- statement:
--   A graph estimator is a numerical streaming machine whose updates are graph insertions or arriving vertices, and whose public parameters include the graph bipartition. For every fixed legal stream representing $G$, two-sided correctness at factor $c$ requires
--
--   $$\Pr\!\left[\operatorname{mm}(G)/c\le\widehat v\le c\operatorname{mm}(G)\right]\ge2/3.$$
--
--   The separate mixed requirement replaces the upper endpoint by $c\operatorname{vc}(G)$, as in Equation (1). Both are required on each simple bipartite input and each supplied valid bipartition, rather than on average over a hard distribution. An empty graph requires output zero on successful executions.
--
--   The two events share one operational execution law and remain distinct throughout the milestones.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §1.1, Equation (1), printed pp.1–2 (PDF pp.2–3). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_GraphStreams
import Definitions.Def_CoarseMatching_LowerBound_StreamingMachine

open MeasureTheory

namespace CoarseMatching.LowerBound
noncomputable section

/-- Graph-stream numerical estimator with public bipartition parameters. -/
abbrev Estimator (n S : ℕ) := StreamingMachine (Update n) (Fin n → Bool) S

/-- Two-sided matching estimate, or the weaker mixed matching/cover requirement
of Equation (1), printed p.2 / PDF p.3. Success is on every fixed legal stream. -/
def Correct {n S : ℕ} (A : Estimator n S) (mode : Arrival) (p : ℕ)
    (c : ℝ) (mixed : Bool) : Prop :=
  ∀ (color : Fin n → Bool) (s : List (Update n)), Legal mode s →
    Respects color (streamGraph s) →
    ENNReal.ofReal (2 / 3 : ℝ) ≤ (A.law p color s)
      (Set.Icc ((mm (streamGraph s) : ℝ) / c)
        (c * (if mixed then (vc (streamGraph s) : ℝ) else (mm (streamGraph s) : ℝ))))

end
end CoarseMatching.LowerBound


