-- Prove2me | Definitions.Def_MetricMinTest_Supplement_mixedWorkload
-- name    : MetricMinTest_Supplement_mixedWorkload
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:34.285519+00:00
-- url     : https://prove2.me/theorems/f29d27a1-e300-49e8-99cc-4fd10d8b4d4f
-- title:
--   Mixed workload $J_d(\gamma)$, program (7.1)
-- statement:
--   The **mixed (regional) workload** is the value of the finite fractional-cover program
--   $$J_d(\gamma)=\min_{y\ge0}\Big\{\sum_{(Z,r)\in\mathcal A}y_{Z,r}\,c(Z,r)\ :\ \sum_{(Z,r):\,i\in S(Z,r)}y_{Z,r}\ge1\ \text{for every }i\Big\},$$
--   over the admissible regions (nonempty $Z$, $r<\gamma$ an occurring distance) with regional cost $c(Z,r)=H_{Z,r}(1+\ln\rho_{Z,r})$.
--
--   It interpolates between ball certificates (singleton regions give $F$) and whole-space screening, and governs the regional upper bounds of Theorems E and 7.3.
--
--   **Formalization Note** The minimum is written as the real infimum of the costs of feasible regional covers; the program is feasible and the paper notes the optimum is attained (p.17).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (7.1), p.16

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_IsRegionalCover
import Definitions.Def_MetricMinTest_Supplement_regionalCoverCost

namespace MetricMinTest.Supplement

/-- **Mixed workload `J_d(γ)`**, program (7.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (7.1), p.16:
`J_d(γ) = min_{y≥0} {∑_{(Z,r)∈A} y_{Z,r} c(Z, r) : ∑_{(Z,r): i∈S(Z,r)} y_{Z,r} ≥ 1 ∀ i}`.

**Formalization Note.** The minimum is the real `sInf` of the costs of feasible regional covers
(`IsRegionalCover`, `regionalCoverCost`). The program is finite; for a pseudometric and
`γ > 0` it is feasible (singleton regions at radius zero) and the paper shows the optimum is
attained (p.17), so `sInf` is that minimum. -/
noncomputable def mixedWorkload {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (γ : ℝ) :
    ℝ :=
  sInf {C : ℝ | ∃ y, IsRegionalCover d γ y ∧ regionalCoverCost d γ y = C}

end MetricMinTest.Supplement


