-- Prove2me | Definitions.Def_GreedyReusableNet_avgReward
-- name    : GreedyReusableNet_avgReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:51.125983+00:00
-- url     : https://prove2.me/theorems/2556d56c-ef19-4c63-9d76-00545c4ca2e0
-- title:
--   Average reward per arm $\bar r_t(B;n(B))=r_t(B;n(B))/|B|$
-- statement:
--   $$\bar r_t(B;n(B))=\frac{r_t(B;n(B))}{|B|},$$
--   the average reward per arm of bundle $B$.
--
--   **Formalization Note** For the empty bundle Lean's division returns $0$, while the paper's $\bar r$ is undefined there; the statement that uses bounds on $\bar r$ (Theorem 2 (6)) assumes nonempty bundles.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.3, p.15

import Mathlib
import Definitions.Def_GreedyReusableNet_PeriodData

namespace GreedyReusableNet

/-- **The average reward per arm** `r̄_t(B; n(B)) = r_t(B; n(B))/|B|` (Simchi-Levi, Zheng & Zhu,
SSRN 3981123, §2.3, p.15).

**Formalization Note** For the empty bundle Lean's division gives `0`; the paper's `r̄` is
undefined there, and the statements that use `r̄` as a bound (Theorem 2 (6)) assume nonempty
bundles. -/
noncomputable def avgReward {N : ℕ} (d : PeriodData N) (B : Finset (Fin N)) (n : Fin N → ℕ) : ℝ :=
  d.reward B n / B.card

end GreedyReusableNet


