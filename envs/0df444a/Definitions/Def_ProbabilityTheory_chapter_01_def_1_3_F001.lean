-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
-- name    : ProbabilityTheory_chapter_01_def_1_3_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T18:46:35.075967+00:00
-- url     : https://prove2.me/theorems/d9382348-a56f-4ce1-921f-e825bf258913
-- title:
--   Chapter 1, def_1_3: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `def_1_3`: `stepIndicator`, `discreteCDF`, `sourceHypotheses_zero_integrator`, `taggedCommonLimit_zero`, `rsIntegrable_zero`, and 5 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

noncomputable def stepIndicator (c x : ℝ) : ℝ :=
  if c ≤ x then 1 else 0

noncomputable def discreteCDF (m : ℕ) (c p : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin m, p i * stepIndicator (c i) x














end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation


