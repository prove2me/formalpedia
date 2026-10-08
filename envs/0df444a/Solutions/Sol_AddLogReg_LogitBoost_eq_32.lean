-- Prove2me | solution 1 for AddLogReg.LogitBoost.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:03:55.851136+00:00
-- url     : https://prove2.me/submissions/abff142c-91db-4d14-a076-b81b44c1dabc

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

open AddLogReg.LogitBoost

private lemma bool_integral (μ : Measure Bool) [IsFiniteMeasure μ] (f : Bool → ℝ) :
    (∫ b, f b ∂μ) = (μ {false}).toReal * f false + (μ {true}).toReal * f true := by
  rw [integral_fintype Integrable.of_finite]
  simp [Fintype.sum_bool, Measure.real, smul_eq_mul, add_comm]

private lemma logistic_form (t : ℝ) :
    symLogistic t = Real.exp (2 * t) / (1 + Real.exp (2 * t)) := by
  unfold symLogistic
  have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [two_mul, Real.exp_add]
  have hi : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  have h3 := Real.exp_pos (2 * t)
  field_simp
  rw [show t * 2 = 2 * t by ring, he]
  nlinarith


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (F : X → ℝ) (x : X) :
    HasDerivAt (condLogLik ν F x)
      (2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) 0 := by
  have hd (t : ℝ) : 1 + Real.exp (2 * (F x + t)) ≠ 0 := by positivity
  have hl (b : Bool) :
      HasDerivAt (fun t : ℝ => 2 * ystar b * (F x + t) -
        Real.log (1 + Real.exp (2 * (F x + t))))
        (2 * (ystar b - symLogistic (F x))) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_add (F x)).const_mul (2 : ℝ)).exp
    have hh := (h.const_add 1).log (hd 0)
    convert (((hasDerivAt_id (0 : ℝ)).const_add (F x)).const_mul (2 * ystar b)).sub hh using 1 <;>
      first | rfl | (funext u; dsimp; ring) | (dsimp; rw [logistic_form]; ring) | ring
  have he : condLogLik ν F x = fun t =>
      (ν.condKernel x {false}).toReal *
        (2 * ystar false * (F x + t) - Real.log (1 + Real.exp (2 * (F x + t)))) +
      (ν.condKernel x {true}).toReal *
        (2 * ystar true * (F x + t) - Real.log (1 + Real.exp (2 * (F x + t)))) := by
    funext t
    exact bool_integral _ _
  rw [he, bool_integral]
  convert ((hl false).const_mul ((ν.condKernel x {false}).toReal)).add
    ((hl true).const_mul ((ν.condKernel x {true}).toReal)) using 1 <;>
      first | rfl | (funext u; dsimp; ring) | (dsimp; ring) | ring

#print axioms solution
