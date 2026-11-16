-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_ActualThreshold
-- name    : RankingQueryCost_Joint_Supplement_ActualThreshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:26.94982+00:00
-- url     : https://prove2.me/theorems/035ec4ad-b00f-430f-8298-a2738712839e
-- title:
--   Full-information actual squared-error threshold
-- statement:
--   Let $K_T$ be the output distribution of a randomized full-information estimator on a complete table $T$. The optimal actual squared-error threshold is
--
--   $$M_{\rm act}(n,s)=\inf\{S\ge0:\exists K\ \forall T\ \forall r\in C_s(T),\ K_T\{q:D^2(q,r)\le S\}\ge3/4\}.$$
--
--   Outputs range over all continuous estimates in $Q$. The same kernel must succeed in every complete-table world, so a true rank is not an input to the estimator. The infimum is taken in the extended nonnegative reals; infeasibility would have value $+\infty$. In fact bounded $Q$ and a constant fallback estimator make the feasible set nonempty with finite targets.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.2, p. 4, PDF p. 5

import Definitions.Def_RankingQueryCost_Joint_Supplement_FullEstimator

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- §2.2: infimum of attainable squared-error targets at success probability 3/4.
Every complete-table world is tested, with the same estimator law for a shared table.
An empty feasible set would give +∞, never an artificial real infimum of zero. -/
def actualThreshold (n s : ℕ) : ENNReal :=
  sInf {S : ENNReal | ∃ K : FullEstimator n,
    ∀ (T : Tournament n) (r : Rank n), r ∈ compatible s (completeTranscript T) →
      (3 / 4 : ENNReal) ≤ K.law T
        {q | ENNReal.ofReal (squaredError q.val (rankVector r)) ≤ S}}

end RankingQueryCost.Joint.Supplement


