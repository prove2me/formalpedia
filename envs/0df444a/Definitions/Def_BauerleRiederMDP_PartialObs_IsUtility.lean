-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_IsUtility
-- name    : BauerleRiederMDP_PartialObs_IsUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:33.815131+00:00
-- url     : https://prove2.me/theorems/c45c3d7e-b8ff-41bd-834f-63b385f6d8e7
-- title:
--   Utility function (Definition 3.4.1)
-- statement:
--   A function $U:\operatorname{dom}U\to\mathbb R$ is a utility function if $U$ is strictly increasing, strictly concave and continuous on $\operatorname{dom}U$. For $\operatorname{dom}U=[0,\infty)$ continuity on the domain includes right-continuity at $0$.
--
--   **Formalization Note** $U$ is a function $\mathbb R\to\mathbb R$ of which only the values on $\operatorname{dom}U$ matter.
-- source:
--   Bäuerle & Rieder (2011), Definition 3.4.1, p.70 (PDF 84)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Utility function.**
Bäuerle & Rieder (2011), Definition 3.4.1, p.70 (PDF 84): "A function `U : dom U → ℝ` is called a
utility function, if `U` is strictly increasing, strictly concave and continuous on `dom U`."
(For `dom U = [0, ∞)` continuity on `dom U` includes right-continuity at `0`, p.71.)

**Formalization Note.** `U` is a function `ℝ → ℝ`; only its values on `domU` matter. -/
def IsUtility (domU : Set ℝ) (U : ℝ → ℝ) : Prop :=
  StrictMonoOn U domU ∧ StrictConcaveOn ℝ domU U ∧ ContinuousOn U domU

end BauerleRiederMDP.PartialObs


