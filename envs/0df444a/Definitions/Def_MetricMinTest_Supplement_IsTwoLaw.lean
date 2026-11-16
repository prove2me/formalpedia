-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsTwoLaw
-- name    : MetricMinTest_Supplement_IsTwoLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:35:19.116201+00:00
-- url     : https://prove2.me/theorems/95007c31-669f-4b64-9d7a-4238ddd3167a
-- title:
--   Two-law class $\mathcal P_2$
-- statement:
--   $\mathcal P_2$ contains the instances whose laws take at most two distinct values, $|\{P_i: i\in[k]\}|\le2$, with unknown assignment of the two laws to indices and no metric constraint. It is the class of Theorem J.1.
--
--   **Formalization Note** Written as: there are laws $Q_1,Q_2$ (possibly equal) with $P_i\in\{Q_1,Q_2\}$ for every $i$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem J.1, p.31

import Mathlib
import Definitions.Def_MetricMinTest_Instance

namespace MetricMinTest.Supplement

/-- **Two-law class `P₂`** (Theorem J.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem J.1, p.31: "Let P₂ contain instances
whose laws take at most two distinct values, with unknown assignment."

**Formalization Note.** `|{Pᵢ : i}| ≤ 2`, written as: there are two laws `Q₁, Q₂` (possibly
equal) with every `Pᵢ ∈ {Q₁, Q₂}`. No metric constraint. -/
def IsTwoLaw {ι : Type} (P : Instance ι) : Prop :=
  ∃ Q₁ Q₂ : MeasureTheory.Measure ℝ, ∀ i, P.law i = Q₁ ∨ P.law i = Q₂

end MetricMinTest.Supplement


