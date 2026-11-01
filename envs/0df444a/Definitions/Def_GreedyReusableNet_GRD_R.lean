-- Prove2me | Definitions.Def_GreedyReusableNet_GRD_R
-- name    : GreedyReusableNet_GRD_R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:04.781021+00:00
-- url     : https://prove2.me/theorems/0bb3c501-0cf1-4813-a7fb-68a36ffd2ee1
-- title:
--   Algorithm 3: the GRD-R policy
-- statement:
--   **GRD-R.** Draw a threshold $r$ from the law with distribution function $G(x)=(1+\ln(x/r_{\min}))/(1+\ln R)$ on $[r_{\min},r_{\max}]$, $R=r_{\max}/r_{\min}$. Then, in every period $t$, use the $(\alpha,\beta)$-oracle to solve
--   $$\max_{\mathcal A_t\in\mathscr A_t,\ \mathcal A_t\text{ available}}\ \sum_{B\in\mathcal A_t}r_t(B;n_t(B))\,\mathbb 1\{r_t(B;n_t(B))\ge r\}\,\mathbb P_t(B\mid\mathcal A_t,n_t(B)),$$
--   eliminate every $B$ of the solution with $r_t(B;n_t(B))<r$, take the action and collect the rewards. The threshold is drawn once, before the first period.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.1, Algorithm 3, p.17

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule
import Definitions.Def_GreedyReusableNet_greedyStep
import Definitions.Def_GreedyReusableNet_avgReward
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

namespace GreedyReusableNet

/-- **Algorithm 3, the GRD-R policy** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, p.17):

1. draw a threshold `r` from the law with distribution function
   `G(x) = (1 + ln(x/r_min))/(1 + ln R)`, `x ∈ [r_min, r_max]`, `R = r_max/r_min`;
2. for `t = 1, 2, …`:
3. use the `(α, β)`-oracle to solve
   `max_{𝒜_t ∈ 𝒜_t, 𝒜_t available} ∑_{B ∈ 𝒜_t} r_t(B; n_t(B)) 𝟙{r_t(B; n_t(B)) ≥ r} ℙ_t(B|𝒜_t, n_t(B))`;
4. eliminate any `B` with `r_t(B; n_t(B)) < r`;
5. take the action and collect the rewards.

The threshold is the policy's initial seed, drawn once before the first period from
`thresholdLaw rmin rmax`. -/
noncomputable def GRD_R {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (rmin rmax : ℝ) :
    Rule N where
  seedLaw := thresholdLaw rmin rmax
  act := fun r t h u =>
    greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts h) (freeArms h t) u

end GreedyReusableNet


