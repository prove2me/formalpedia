-- Prove2me | Definitions.Def_HighDimStat_UniformLaws_IsRademacherVariable
-- name    : HighDimStat_UniformLaws_IsRademacherVariable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:26:14.597052+00:00
-- url     : https://prove2.me/theorems/01d3c116-c780-4828-8961-b5bd3d1467e6
-- title:
--   A Rademacher random variable
-- statement:
--   A **Rademacher variable** $\varepsilon$: $\mathbb P[\varepsilon=1]=\mathbb P[\varepsilon=-1]=1/2$,
--   used throughout the symmetrization argument of Section 4.2 to define the empirical
--   Rademacher complexity.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 23 (PDF p. 43), Example 2.3

import Mathlib

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- A **Rademacher variable**: `P[ε=1] = P[ε=-1] = 1/2`, Wainwright, *High-Dimensional
Statistics* (2019), used throughout the symmetrization argument of Section 4.2. -/
def IsRademacherVariable {Ω : Type*} [MeasurableSpace Ω] (eps : Ω → ℝ) (Prob : Measure Ω) :
    Prop :=
  Prob.real {ω | eps ω = 1} = 1 / 2 ∧ Prob.real {ω | eps ω = -1} = 1 / 2

end HighDimStat.UniformLaws


