-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
-- name    : ProbabilityTheory_chapter_01_def_1_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T18:46:15.377583+00:00
-- url     : https://prove2.me/theorems/c5e83da7-661b-495f-93e4-cb1798b1a045
-- title:
--   Definition 1.3: Expectation and variance via Stieltjes integrals
-- statement:
--   For a cumulative distribution function F on [a,b], expectation integrates x with respect to F; variance integrates the squared deviation from that expectation. Integrability witnesses are explicit parameters.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

noncomputable def cdfExpectation
    (a b : ℝ) (F : ℝ → ℝ)
    (h_int : RSIntegrable (fun x => x) F a b) : ℝ :=
  rsIntegral (fun x => x) F a b h_int

noncomputable def cdfVariance (a b : ℝ) (F : ℝ → ℝ)
    (h_int_exp : RSIntegrable (fun x => x) F a b)
    (h_int_var : RSIntegrable (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b) : ℝ :=
  rsIntegral (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b h_int_var
end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation


