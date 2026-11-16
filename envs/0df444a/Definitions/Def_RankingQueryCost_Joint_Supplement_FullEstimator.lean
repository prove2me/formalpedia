-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_FullEstimator
-- name    : RankingQueryCost_Joint_Supplement_FullEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:52.830201+00:00
-- url     : https://prove2.me/theorems/38040e2c-2560-4a7b-9943-3604a2ef93f7
-- title:
--   Randomized full-information ranking estimator
-- statement:
--   A full-information estimator receives only a complete answer table $T$ and chooses a continuous estimate in $Q$ according to a probability distribution $K_T$:
--
--   $$K:T\longmapsto K_T\in\mathcal P(Q).$$
--
--   The distribution may depend on the table but cannot depend on which of its compatible orders is the actual order. All probability distributions on $Q$ are allowed. This separates randomized actual estimation from the deterministic compatible-set radius. Since the table domain is finite, a table-indexed family of probability measures is exactly a Markov kernel from tables to $Q$.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.2, p. 4, PDF p. 5

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- A full-information randomized estimator sees precisely the complete answer table.
Its output distribution is an arbitrary probability measure on the continuous Q.
The table space is finite, so no further table-measurability restriction is needed. -/
structure FullEstimator (n : ℕ) where
  law : Tournament n → MeasureTheory.Measure {q // q ∈ estimateSet n}
  probability : ∀ T, MeasureTheory.IsProbabilityMeasure (law T)

end RankingQueryCost.Joint.Supplement


