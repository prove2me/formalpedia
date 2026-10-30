-- Prove2me | Definitions.Def_FreemiumActions_Threshold_ThresholdPolicy
-- name    : FreemiumActions_Threshold_ThresholdPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:59:23.92728+00:00
-- url     : https://prove2.me/theorems/3591c679-0409-40f2-b2a1-d00979a8d17c
-- title:
--   Forward threshold policies including the empty initial segment
-- statement:
--   A forward threshold policy offers at exactly the levels below some initial-segment length $k\in\{0,\ldots,N+1\}$:
--   $$y(e)=1\ \Longleftrightarrow\ e<k.$$
--   Its cutoff in the paper’s notation is $e^*=k-1\in\{-1,\ldots,N\}$. Thus $k=0$ removes the offer everywhere, and $k=N+1$ offers everywhere. This is a property of a policy, separate from revenue optimality. There is no tie-breaking or uniqueness convention.
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §5, pp. 17 and 19–21 (PDF pp. 17 and 19–21), threshold discussion and Theorem 2; catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Values

namespace FreemiumActions.Threshold

def IsThreshold {N : ℕ} (y : Policy N) : Prop :=
  ∃ k : Fin (N + 2), ∀ e : Level N, y e = decide (e.val < k.val)

end FreemiumActions.Threshold


