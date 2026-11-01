-- Prove2me | Definitions.Def_GreedyReusableNet_GRDbar_R
-- name    : GreedyReusableNet_GRDbar_R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:02.714988+00:00
-- url     : https://prove2.me/theorems/d2fc999c-81d8-4f42-932a-e607b1fb227d
-- title:
--   Algorithm 4: the $\overline{\mathrm{GRD}}$-R policy
-- statement:
--   **$\overline{\mathrm{GRD}}$-R.** Draw a threshold $\bar r$ from the law with distribution function $\bar G(x)=(1+\ln(x/\bar r_{\min}))/(1+\ln\bar R)$ on $[\bar r_{\min},\bar r_{\max}]$, $\bar R=\bar r_{\max}/\bar r_{\min}$. Then, in every period $t$, use the $(\alpha,\beta)$-oracle to solve
--   $$\max_{\mathcal A_t\in\mathscr A_t,\ \mathcal A_t\text{ available}}\ \sum_{B\in\mathcal A_t}r_t(B;n_t(B))\,\mathbb 1\{\bar r_t(B;n_t(B))\ge\bar r\}\,\mathbb P_t(B\mid\mathcal A_t,n_t(B)),$$
--   eliminate every $B$ with $\bar r_t(B;n_t(B))<\bar r$, take the action and collect the rewards. The oracle weight is the total reward; the threshold acts on the average reward per arm.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.1, Algorithm 4, p.17

import Mathlib
import Definitions.Def_GreedyReusableNet_run
import Definitions.Def_GreedyReusableNet_Rule
import Definitions.Def_GreedyReusableNet_greedyStep
import Definitions.Def_GreedyReusableNet_avgReward
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

namespace GreedyReusableNet

/-- **Algorithm 4, the GRD̄-R policy** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, p.17): as GRD-R, but the threshold `r̄` is
drawn from `Ḡ(x) = (1 + ln(x/r̄_min))/(1 + ln R̄)`, `x ∈ [r̄_min, r̄_max]`, `R̄ = r̄_max/r̄_min`, the
oracle weight is `r_t(B; n_t(B)) 𝟙{r̄_t(B; n_t(B)) ≥ r̄}` and step 4 eliminates every `B` with
`r̄_t(B; n_t(B)) < r̄`, where `r̄_t = r_t/|B|` (`avgReward`).

The threshold is the policy's initial seed, drawn once before the first period from
`thresholdLaw rbmin rbmax`. -/
noncomputable def GRDbar_R {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (rbmin rbmax : ℝ) :
    Rule N where
  seedLaw := thresholdLaw rbmin rbmax
  act := fun r t h u =>
    greedyStep O avgReward r (I.period t) (counts h) (freeArms h t) u

end GreedyReusableNet


