-- Prove2me | solution 1 for AddLogReg.Gentle.newton_update
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:44:56.315928+00:00
-- url     : https://prove2.me/submissions/d207a208-87e5-4ea5-8934-4e758f1900c2

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory

open AddLogReg.Gentle


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    F x + (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) /
        (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) =
      F x + AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x := by
  rfl



#print axioms solution
