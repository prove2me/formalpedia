-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_Radius
-- name    : RankingQueryCost_Joint_Supplement_Radius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:45:58.546204+00:00
-- url     : https://prove2.me/theorems/43648060-1d33-4773-9b9d-3e963a5591d2
-- title:
--   Complete-table compatible-set squared radius
-- statement:
--   Let $T$ be a complete comparison table on $n$ objects and $C_s(T)$ its compatible rank permutations. Centers range over the full continuous output polytope $Q$, including ties and nonintegral coordinates. Define
--
--   $$\rho_s(T)=\inf_{q\in Q}\sup_{r\in C_s(T)}D^2(q,r).$$
--
--   For nonempty compatible sets, compactness of $Q$ and finiteness of the ranks make these extrema attained. The extended nonnegative real encoding assigns zero to the supremum of an empty compatible set. All source radius claims concern nonempty compatible sets. This is an operational radius, independent of the target formula $U$.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.2, p. 4, PDF p. 5

import Definitions.Def_RankingQueryCost_Joint_Transcript

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- §2.2: squared radius of the complete-table version space, with centers in the
entire continuous output polytope. Extended nonnegative reals make both optima total.
The supremum of an empty compatible set is zero. The theorems use nonempty sets. -/
def radius {n : ℕ} (s : ℕ) (T : Tournament n) : ENNReal :=
  ⨅ q : {q // q ∈ estimateSet n},
    ⨆ r : {r // r ∈ compatible s (completeTranscript T)},
      ENNReal.ofReal (squaredError q.val (rankVector r.val))

end RankingQueryCost.Joint.Supplement


