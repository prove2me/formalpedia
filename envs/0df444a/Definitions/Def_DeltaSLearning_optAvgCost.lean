-- Prove2me | Definitions.Def_DeltaSLearning_optAvgCost
-- name    : DeltaSLearning_optAvgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:08:24.71788+00:00
-- url     : https://prove2.me/theorems/bb17af33-0bde-4feb-a30e-80a61cc7e6a4
-- title:
--   Optimal average pseudo cost $V^*$
-- statement:
--   The optimal long-run average pseudo cost is
--   $$V^* := \min_{0\le\delta\le S\le\beta}V(\delta,S).$$
--   It is the benchmark of the regret: the clairvoyant optimal $(\delta^*,S^*)$ policy of Theorem 1 attains it, with $S^*\le\beta$.
--
--   **Formalization Note** $V^*$ is defined directly as the infimum of $V$ over the feasible pairs, not through Theorem 1 (Zheng 1991), which is cited by the paper and not formalized. The set is nonempty since $\beta\ge0$ and bounded since $|V|\le\gamma$.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (9) and V* := V(δ*,S*), p.11; S* ≤ β, p.9; Table 3, p.34

import Mathlib
import Definitions.Def_DeltaSLearning_avgCost

open MeasureTheory

namespace DeltaSLearning

/-- The optimal long-run average pseudo cost `V* := min_{0 ≤ δ ≤ S ≤ β} V(δ, S)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (9) and `V* := V(δ*, S*)` p.11, "S* ≤ β" p.9, Table 3 p.34.

**Formalization Note** `V*` is the infimum of `V` over the feasible pairs `0 ≤ δ ≤ S ≤ β`,
not `V` at a pair given by Theorem 1 (Zheng 1991), which is cited and not formalized. The set is
nonempty (`β ≥ 0`) and bounded (`|V| ≤ γ`). -/
noncomputable def optAvgCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (cp : Params) : ℝ :=
  sInf {v | ∃ δ S : ℝ, 0 ≤ δ ∧ δ ≤ S ∧ S ≤ cp.β ∧ v = avgCost P D cp δ S}

end DeltaSLearning


