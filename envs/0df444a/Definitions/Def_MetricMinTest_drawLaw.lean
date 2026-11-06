-- Prove2me | Definitions.Def_MetricMinTest_drawLaw
-- name    : MetricMinTest_drawLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:59.271192+00:00
-- url     : https://prove2.me/theorems/f80110c3-c08b-4d4e-961d-27826bcf8dd1
-- title:
--   Sampling law $p=w/W$
-- statement:
--   For an allocation $w\ge0$ of mass $W=\sum_jw_j>0$, the sampling law on indices is $p=w/W$, i.e. index $j$ is drawn with probability $w_j/W$.
--
--   **Formalization Note** The measure $\sum_j(w_j/W)\,\delta_j$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma B.1, p.22; Appendix B, p.23

import Mathlib

namespace MetricMinTest

/-- **Sampling law `p = w/W`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC
2027 submission (manuscript sha256 dcece193…ad32bb), Lemma B.1, p.22 ("Put p = w/W"), the shared
tester (p.23: "draw Iₜ ∼ w/W") and TwoPhase/TwoRound (pp.23, 25).

**Formalization Note.** `∑ⱼ (wⱼ / W) δⱼ` with `W = ∑ⱼ wⱼ`; a probability measure when `w ≥ 0` and
`W > 0`, the hypotheses of every result that uses it. -/
noncomputable def drawLaw {ι : Type} [Fintype ι] [MeasurableSpace ι] (w : ι → ℝ) :
    MeasureTheory.Measure ι :=
  ∑ j, ENNReal.ofReal (w j / ∑ j', w j') • MeasureTheory.Measure.dirac j

end MetricMinTest


