-- Prove2me | Definitions.Def_GreedyReusableNet_GRD
-- name    : GreedyReusableNet_GRD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:48.309109+00:00
-- url     : https://prove2.me/theorems/9ff35fc7-a69e-4a59-ad2b-99bcd2be110e
-- title:
--   $\mathrm{GRD}(r)$: greedy policy with fixed threshold $r$ on the total reward
-- statement:
--   For a fixed threshold $r$, the policy $\mathrm{GRD}(r)$ runs in every period the threshold-greedy step with the score $r_t(B;n(B))$: it calls the oracle with weights $r_t(B;n_t(B))\,\mathbb 1\{r_t(B;n_t(B))\ge r\}$ on the available action sets and eliminates the bundles with $r_t(B;n_t(B))<r$. It is GRD-R conditioned on its threshold, the object of (12) in the proof of Theorem 2.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, proof of Theorem 2, p.40; Algorithm 3 steps 2–6, p.17

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule
import Definitions.Def_GreedyReusableNet_greedyStep
import Definitions.Def_GreedyReusableNet_avgReward

open MeasureTheory

namespace GreedyReusableNet

/-- **`GRD(r)`, the greedy policy with a fixed threshold `r` on the total reward** (Simchi-Levi,
Zheng & Zhu, SSRN 3981123, proof of Theorem 2, p.40: "Let `GRD(r)` be the greedy policy when the
random threshold for total reward is `r`"; Algorithm 3 steps 2–6, p.17, with `r` given).

In period `t` with history `h` it runs `greedyStep` on period `t`'s data, the counting vector
`counts h` and the available arms `freeArms h t`, with the score `r_t(B; n(B))`.

**Formalization Note** The initial seed is unused (its law is the point mass at `0`); the period
seed is the oracle's seed. -/
noncomputable def GRD {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) : Rule N where
  seedLaw := Measure.dirac 0
  act := fun _ t h u =>
    greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts h) (freeArms h t) u

end GreedyReusableNet


