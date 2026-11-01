-- Prove2me | Definitions.Def_GreedyReusableNet_GRDbar
-- name    : GreedyReusableNet_GRDbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:41.863217+00:00
-- url     : https://prove2.me/theorems/56ad977b-3e7b-4f10-9d3f-0f36fdde5c8d
-- title:
--   $\overline{\mathrm{GRD}}(\bar r)$: greedy policy with fixed threshold $\bar r$ on the average reward
-- statement:
--   For a fixed threshold $\bar r$, the policy $\overline{\mathrm{GRD}}(\bar r)$ runs in every period the threshold-greedy step with the score $\bar r_t(B;n(B))=r_t(B;n(B))/|B|$: oracle weights $r_t(B;n_t(B))\,\mathbb 1\{\bar r_t(B;n_t(B))\ge\bar r\}$, then elimination of the bundles with $\bar r_t(B;n_t(B))<\bar r$. It is $\overline{\mathrm{GRD}}$-R conditioned on its threshold, the object of (13).
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, p.42; Algorithm 4 steps 2–6, p.17

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule
import Definitions.Def_GreedyReusableNet_greedyStep
import Definitions.Def_GreedyReusableNet_avgReward

open MeasureTheory

namespace GreedyReusableNet

/-- **`GRD̄(r̄)`, the greedy policy with a fixed threshold `r̄` on the average reward per arm**
(Simchi-Levi, Zheng & Zhu, SSRN 3981123, proof of Theorem 2, p.42: "Let `GRD̄(r̄)` be the greedy policy when the random
threshold for average reward is `r̄`"; Algorithm 4 steps 2–6, p.17, with `r̄` given): as `GRD`
with the score `r̄_t(B; n(B)) = r_t(B; n(B))/|B|` (`avgReward`); the oracle weight stays the
total reward `r_t(B; n(B)) 𝟙{r̄_t(B; n(B)) ≥ r̄}`.

**Formalization Note** The initial seed is unused (its law is the point mass at `0`); the period
seed is the oracle's seed. An empty bundle has `r̄ = 0` in Lean, so it is never kept for `r̄ > 0`. -/
noncomputable def GRDbar {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) : Rule N where
  seedLaw := Measure.dirac 0
  act := fun _ t h u =>
    greedyStep O avgReward r (I.period t) (counts h) (freeArms h t) u

end GreedyReusableNet


