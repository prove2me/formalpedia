-- Prove2me | Definitions.Def_DeltaSLearning_optAvgCostGap
-- name    : DeltaSLearning_optAvgCostGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:08:29.105299+00:00
-- url     : https://prove2.me/theorems/8748c2ca-e898-4c73-b67b-54266353ce3b
-- title:
--   Optimized objective $V^*(\delta)=\min_{S\in[\delta,\beta]}V(\delta,S)$
-- statement:
--   For a gap $\delta$,
--   $$V^*(\delta) := \min_{S\in[\delta,\beta]}V(\delta,S),$$
--   the best long-run average pseudo cost over targets for that gap (12). On the grid, $V^*_j:=V^*(\delta_j)$.
--
--   **Formalization Note** The minimum is written as the infimum of the image of $[\delta,\beta]$. For $0\le\delta\le\beta$ this set is nonempty and bounded ($|V|\le\gamma$), and by Theorem 2(a) the infimum is attained, so it is the paper's minimum.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (12), p.12; V*_j, p.23

import Mathlib
import Definitions.Def_DeltaSLearning_avgCost

open MeasureTheory

namespace DeltaSLearning

/-- `V*(δ) := min_{S ∈ [δ, β]} V(δ, S)` of (12), the objective in the gap `δ` with the target
optimized; `V*_j := V*(δ_j)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (12), p.12; `V*_j`, p.23.

**Formalization Note** The minimum is encoded as `sInf` of the image of `[δ, β]`. For
`0 ≤ δ ≤ β` the set is nonempty and bounded (`|V| ≤ γ`), and by Theorem 2(a) the infimum is
attained, so it is the paper's minimum. -/
noncomputable def optAvgCostGap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → ℝ) (cp : Params) (δ : ℝ) : ℝ :=
  sInf ((fun S => avgCost P D cp δ S) '' Set.Icc δ cp.β)

end DeltaSLearning


