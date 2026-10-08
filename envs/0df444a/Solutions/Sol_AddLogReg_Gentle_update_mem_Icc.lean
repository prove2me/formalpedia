-- Prove2me | solution 1 for AddLogReg.Gentle.update_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:57.35427+00:00
-- url     : https://prove2.me/submissions/e6ae2fd6-aeb8-4c0b-b958-176f8f43da8c

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
    AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [AddLogReg.ExpCrit.wCondExp, bool_integral, bool_integral]
  simp only [AddLogReg.ExpCrit.sgn, neg_one_mul, neg_neg, one_mul, mul_neg_one, mul_one, mul_neg]
  let a := (ν.condKernel x {false}).toReal * Real.exp (F x)
  let b := (ν.condKernel x {true}).toReal * Real.exp (-F x)
  have ha : 0 ≤ a := mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _))
  have hb : 0 ≤ b := mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _))
  change (-a + b) / (a + b) ∈ Set.Icc (-1 : ℝ) 1
  by_cases h : a + b = 0
  · simp [h]
  · have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    constructor
    · apply (le_div_iff₀ hp).2
      linarith
    · apply (div_le_iff₀ hp).2
      linarith

#print axioms solution
