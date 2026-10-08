-- Prove2me | solution 1 for AddLogReg.Gentle.update_eq_wprob_diff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:58.756599+00:00
-- url     : https://prove2.me/submissions/d2d4b532-b84c-4d45-a677-53efb4c89933

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

open AddLogReg.Gentle

private lemma bool_integral (μ : Measure Bool) [IsFiniteMeasure μ] (f : Bool → ℝ) :
    (∫ b, f b ∂μ) = (μ {false}).toReal * f false + (μ {true}).toReal * f true := by
  rw [integral_fintype Integrable.of_finite]
  simp [Fintype.sum_bool, Measure.real, smul_eq_mul, add_comm]


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x = wProb ν F true x - wProb ν F false x := by
  simp only [AddLogReg.ExpCrit.wCondExp, wProb, bool_integral]
  simp [AddLogReg.ExpCrit.sgn]
  ring

#print axioms solution
