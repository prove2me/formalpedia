-- Prove2me | Definitions.Def_MetricMinTest_Supplement_regionalCoverCost
-- name    : MetricMinTest_Supplement_regionalCoverCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:31:38.54425+00:00
-- url     : https://prove2.me/theorems/dd32fbb6-5e45-4ad8-8217-c1337a41b58c
-- title:
--   Cost of a regional cover
-- statement:
--   The **cost** of a weighting $y$ of the admissible regions is $\sum_{(Z,r)\in\mathcal A}y_{Z,r}\,c(Z,r)$, with the regional cost $c(Z,r)=H_{Z,r}(1+\ln\rho_{Z,r})$.
--
--   **Formalization Note** Region indexing as in the regional-cover predicate.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), (7.1), p.16

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_regionCost

namespace MetricMinTest.Supplement

/-- **Cost of a regional cover**, `∑_{(Z,r)∈A} y_{Z,r} c(Z, r)` (program (7.1)). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (7.1),
p.16.

**Formalization Note.** Region indexing as in `IsRegionalCover`: `(Z, (i₀, j₀))`, radius
`d i₀ j₀`, admissible when `Z` is nonempty and `d i₀ j₀ < γ`. -/
noncomputable def regionalCoverCost {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (γ : ℝ) (y : Finset ι × (ι × ι) → ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Finset ι × (ι × ι) => q.1.Nonempty ∧ d q.2.1 q.2.2 < γ),
    y q * regionCost d γ q.1 (d q.2.1 q.2.2)

end MetricMinTest.Supplement


