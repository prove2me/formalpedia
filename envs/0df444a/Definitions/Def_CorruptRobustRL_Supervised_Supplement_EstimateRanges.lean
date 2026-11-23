-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_EstimateRanges
-- name    : CorruptRobustRL_Supervised_Supplement_EstimateRanges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:10:28.346027+00:00
-- url     : https://prove2.me/theorems/7d407c6b-758a-4933-b939-98c95dc8e6f1
-- title:
--   Coordinatewise ranges of the abstract model estimate
-- statement:
--   For a horizon $H$ and a raw model estimate $m=(\widehat r,\widehat p,b)$, the range predicate means that for all states $x,y$ and actions $a$,
--   $$0\le\widehat r(x,a)\le1,\qquad0\le\widehat p(y\mid x,a)\le1,\qquad0\le b(x,a)\le H.$$
--   These are the source's model-estimate ranges, used by Condition C.2. The transition estimates have coordinatewise bounds; the predicate imposes no row-sum normalization. This uses the published raw model-estimate structure rather than its stronger empirical-probability predicate.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 16, model-estimate paragraph following Definition 4.6

import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type}

/-- The model-estimate ranges on p. 16, used by C.2: coordinatewise [0,1]
for estimated transitions, with no row-sum normalization premise. -/
def HasEstimateRanges (H : ℕ) (m : ModelEst X A) : Prop :=
  ∀ x a, (0 ≤ m.r x a ∧ m.r x a ≤ 1) ∧
    (∀ y, 0 ≤ m.p x a y ∧ m.p x a y ≤ 1) ∧
    (0 ≤ m.b x a ∧ m.b x a ≤ (H : ℝ))

end CorruptRobustRL.Supervised.Supplement


