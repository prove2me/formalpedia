-- Prove2me | Definitions.Def_GreedyReusableNet_greedyStep
-- name    : GreedyReusableNet_greedyStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:30.376823+00:00
-- url     : https://prove2.me/theorems/b7b9bfdf-0726-4f12-ab96-687f909899eb
-- title:
--   One period of a threshold-greedy policy
-- statement:
--   Given a threshold $r$ and a score $s(B)$ of each bundle, one period of the threshold-greedy rule is:
--
--   1. call the oracle with weights $f(B)=r_t(B;n(B))\,\mathbb 1\{s(B)\ge r\}$ over the available action sets;
--   2. eliminate from the returned action set every bundle with $s(B)<r$.
--
--   Algorithm 3 (GRD-R) uses the total reward $s(B)=r_t(B;n(B))$; Algorithm 4 ($\overline{\mathrm{GRD}}$-R) uses the average reward per arm $s(B)=\bar r_t(B;n(B))$, while the oracle weight stays the total reward. The step reads only the current period's data, counts and available arms.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.1, Algorithms 3 and 4, steps 3–4, p.17

import Mathlib
import Definitions.Def_GreedyReusableNet_Oracle

namespace GreedyReusableNet

/-- **One period of a threshold-greedy policy** (Simchi-Levi, Zheng & Zhu, SSRN 3981123,
Algorithms 3 and 4, steps 3–4, p.17), with threshold `r` on the score `score d B n` of a bundle:

* step 3: call the oracle on the period data `d`, the counts `n` and the available arms `free`
  with weights `f(B) = r_t(B; n(B)) · 𝟙{score(B) ≥ r}`;
* step 4: eliminate from the returned action set every bundle with `score(B) < r`.

Algorithm 3 (GRD-R) uses the total reward `score = r_t(B; n(B))`; Algorithm 4 (GRD̄-R) uses the
average reward per arm `score = r̄_t(B; n(B)) = r_t(B; n(B))/|B|`, while the oracle weight is
still the total reward `r_t`. The step reads one period's data only. -/
noncomputable def greedyStep {N : ℕ} (O : Oracle N)
    (score : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ) (r : ℝ) (d : PeriodData N)
    (n : Fin N → ℕ) (free : Finset (Fin N)) (u : ℝ) : Finset (Finset (Fin N)) := by
  classical
  exact (O.sel d (fun B => d.reward B n * (if r ≤ score d B n then 1 else 0)) n free u).filter
    (fun B => r ≤ score d B n)

end GreedyReusableNet


