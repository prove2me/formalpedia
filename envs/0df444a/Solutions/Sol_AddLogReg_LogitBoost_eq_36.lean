-- Prove2me | solution 1 for AddLogReg.LogitBoost.eq_36
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:38:34.714215+00:00
-- url     : https://prove2.me/submissions/99767c14-c0bd-4485-99d0-0eb28a917943

import Mathlib
import Definitions.Def_AddLogReg_Gentle_Setting

open MeasureTheory ProbabilityTheory
open AddLogReg.LogitBoost

set_option maxRecDepth 2048

private lemma bool_integral (μ : Measure Bool) [IsFiniteMeasure μ] (f : Bool → ℝ) :
    (∫ b, f b ∂μ) = (μ {false}).toReal * f false + (μ {true}).toReal * f true := by
  rw [integral_fintype Integrable.of_finite]
  simp [Fintype.sum_bool, Measure.real, smul_eq_mul, add_comm]

private lemma bool_mass (μ : Measure Bool) [IsProbabilityMeasure μ] :
    (μ {false}).toReal + (μ {true}).toReal = 1 := by
  have h := bool_integral μ (fun _ => 1)
  rw [integral_const, probReal_univ, one_smul] at h
  simpa only [mul_one] using h.symm

private lemma logistic_pos (t : ℝ) : 0 < symLogistic t ∧ symLogistic t < 1 := by
  unfold symLogistic
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by linarith)

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

private lemma logistic_deriv (a t : ℝ) :
    HasDerivAt (fun u : ℝ => symLogistic (a + u))
      (2 * symLogistic (a + t) * (1 - symLogistic (a + t))) t := by
  have he := (((hasDerivAt_id t).const_add a).const_mul (2 : ℝ)).exp
  have hd : 1 + Real.exp (2 * (a + t)) ≠ 0 := by positivity
  have h := he.div (he.const_add 1) hd
  simp_rw [logistic_form]
  convert h using 1 <;> first | rfl | (simp only [id_eq, mul_one]; field_simp <;> ring)

private lemma loglik_deriv {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) (t : ℝ) :
    HasDerivAt (condLogLik ν F x)
      (2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x)) t := by
  have hd (u : ℝ) : 1 + Real.exp (2 * (F x + u)) ≠ 0 := by positivity
  have hl (b : Bool) :
      HasDerivAt (fun u : ℝ => 2 * ystar b * (F x + u) -
        Real.log (1 + Real.exp (2 * (F x + u))))
        (2 * (ystar b - symLogistic (F x + t))) t := by
    have h := (((hasDerivAt_id t).const_add (F x)).const_mul (2 : ℝ)).exp
    have hh := (h.const_add 1).log (hd t)
    convert (((hasDerivAt_id t).const_add (F x)).const_mul (2 * ystar b)).sub hh using 1 <;>
      first | rfl | (funext u; dsimp; ring) | (dsimp; rw [logistic_form]; ring) | ring
  have he : condLogLik ν F x = fun u =>
      (ν.condKernel x {false}).toReal *
        (2 * ystar false * (F x + u) - Real.log (1 + Real.exp (2 * (F x + u)))) +
      (ν.condKernel x {true}).toReal *
        (2 * ystar true * (F x + u) - Real.log (1 + Real.exp (2 * (F x + u)))) := by
    funext u
    exact bool_integral _ _
  rw [he, bool_integral]
  convert ((hl false).const_mul ((ν.condKernel x {false}).toReal)).add
    ((hl true).const_mul ((ν.condKernel x {true}).toReal)) using 1 <;>
      first | rfl | (funext u; dsimp; ring) | (dsimp; ring) | ring

private lemma loglik_second {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (fun t : ℝ => 2 * ∫ b, (ystar b - symLogistic (F x + t)) ∂(ν.condKernel x))
      (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) 0 := by
  simp_rw [bool_integral]
  have hl (b : Bool) := (hasDerivAt_const (0 : ℝ) (ystar b)).sub (logistic_deriv (F x) 0)
  convert (((hl false).const_mul ((ν.condKernel x {false}).toReal)).add
    ((hl true).const_mul ((ν.condKernel x {true}).toReal))).const_mul (2 : ℝ) using 1 <;>
      first | rfl | (funext u; simp only [add_zero, sub_zero, zero_sub, mul_one] <;> ring) |
        (simp only [add_zero, sub_zero, zero_sub, mul_one] <;> ring)

private lemma logit_weight_pos {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    0 < ∫ _b : Bool, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x) := by
  rw [integral_const, probReal_univ, one_smul]
  exact mul_pos (logistic_pos (F x)).1 (sub_pos.mpr (logistic_pos (F x)).2)

private lemma logit_weight_cancel {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    wCondExpBy ν (logitWeight F) (workingResponse F) x =
      (∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
        (∫ _b : Bool, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x)) := by
  have hp : symLogistic (F x) * (1 - symLogistic (F x)) ≠ 0 :=
    ne_of_gt (mul_pos (logistic_pos (F x)).1 (sub_pos.mpr (logistic_pos (F x)).2))
  unfold wCondExpBy logitWeight workingResponse
  congr 1
  apply integral_congr_ae
  filter_upwards [] with b
  exact mul_div_cancel₀ _ hp

private lemma bool_variance_min (μ : Measure Bool) [IsProbabilityMeasure μ]
    (f : Bool → ℝ) (t : ℝ) :
    (∫ b, (f b - ∫ c, f c ∂μ) ^ 2 ∂μ) ≤ ∫ b, (f b - t) ^ 2 ∂μ := by
  have hm := bool_mass μ
  simp_rw [bool_integral]
  rw [show (μ {true}).toReal = 1 - (μ {false}).toReal by linarith]
  nlinarith [sq_nonneg (t - ((μ {false}).toReal * f false + (1 - (μ {false}).toReal) * f true))]

private lemma gentle_deriv {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) (t : ℝ) :
    HasDerivAt (AddLogReg.Gentle.condCritAt ν F x)
      (-∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) *
        AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) t := by
  have hb (b : Bool) : HasDerivAt
      (fun u : ℝ => Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + u))))
      (-(Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) * AddLogReg.ExpCrit.sgn b)) t := by
    convert ((((hasDerivAt_id t).const_add (F x)).const_mul
      (AddLogReg.ExpCrit.sgn b)).neg).exp using 1 <;> first | rfl | (dsimp; ring)
  unfold AddLogReg.Gentle.condCritAt
  simp_rw [bool_integral]
  convert ((hb false).const_mul ((ν.condKernel x {false}).toReal)).add
    ((hb true).const_mul ((ν.condKernel x {true}).toReal)) using 1 <;>
      first | rfl | ring | (funext u; ring)

private lemma gentle_second {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    HasDerivAt (fun t : ℝ => -∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + t))) *
      AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x))
      (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) 0 := by
  have hb (b : Bool) : HasDerivAt
      (fun u : ℝ => Real.exp (-(AddLogReg.ExpCrit.sgn b * (F x + u))) * AddLogReg.ExpCrit.sgn b)
      (-Real.exp (-(AddLogReg.ExpCrit.sgn b * F x))) 0 := by
    convert (((((hasDerivAt_id (0 : ℝ)).const_add (F x)).const_mul
      (AddLogReg.ExpCrit.sgn b)).neg).exp).mul_const (AddLogReg.ExpCrit.sgn b) using 1 <;>
      first | rfl | (cases b <;> simp [AddLogReg.ExpCrit.sgn])
  simp_rw [bool_integral]
  convert (((hb false).const_mul ((ν.condKernel x {false}).toReal)).add
    ((hb true).const_mul ((ν.condKernel x {true}).toReal))).neg using 1 <;>
      first | rfl | ring | (funext u; ring)

private lemma gentle_pos {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    0 < ∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x) := by
  exact integral_exp_pos Integrable.of_finite

private lemma logit_weighted {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ)
    (g : X → Bool → ℝ) (x : X) :
    wCondExpBy ν (logitWeight F) g x = ∫ b, g x b ∂(ν.condKernel x) := by
  have hp : symLogistic (F x) * (1 - symLogistic (F x)) ≠ 0 :=
    ne_of_gt (mul_pos (logistic_pos (F x)).1 (sub_pos.mpr (logistic_pos (F x)).2))
  unfold wCondExpBy logitWeight
  rw [integral_const_mul, integral_const, probReal_univ, one_smul]
  exact mul_div_cancel_left₀ _ hp

private lemma residual_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) =
      AddLogReg.ExpCrit.condProb ν true x - symLogistic (F x) := by
  have hm := bool_mass (ν.condKernel x)
  rw [bool_integral]
  simp only [ystar, AddLogReg.ExpCrit.condProb]
  rw [show (ν.condKernel x {false}).toReal = 1 - (ν.condKernel x {true}).toReal by linarith]
  ring

private lemma exp_integral_form {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) ∂(ν.condKernel x)) =
      Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x +
        Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x) := by
  have hm := bool_mass (ν.condKernel x)
  rw [bool_integral]
  simp only [AddLogReg.ExpCrit.sgn, AddLogReg.ExpCrit.condProb, one_mul, neg_one_mul, neg_neg]
  rw [show (ν.condKernel x {false}).toReal = 1 - (ν.condKernel x {true}).toReal by linarith]
  ring

private lemma exp_label_integral_form {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) :
    (∫ b, Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * AddLogReg.ExpCrit.sgn b ∂(ν.condKernel x)) =
      Real.exp (-F x) * AddLogReg.ExpCrit.condProb ν true x -
        Real.exp (F x) * (1 - AddLogReg.ExpCrit.condProb ν true x) := by
  have hm := bool_mass (ν.condKernel x)
  rw [bool_integral]
  simp only [AddLogReg.ExpCrit.sgn, AddLogReg.ExpCrit.condProb, one_mul, neg_one_mul, neg_neg, mul_one, mul_neg_one]
  rw [show (ν.condKernel x {false}).toReal = 1 - (ν.condKernel x {true}).toReal by linarith]
  ring

private lemma ratio_reparam (A B P : ℝ) (hS : A + B ≠ 0) :
    (B * P - A * (1 - P)) / (B * P + A * (1 - P)) =
      (P - A / (A + B)) / ((1 - A / (A + B)) * P + A / (A + B) * (1 - P)) := by
  have hn : P - A / (A + B) = (B * P - A * (1 - P)) / (A + B) := by
    field_simp [hS] <;> ring
  have hd : (1 - A / (A + B)) * P + A / (A + B) * (1 - P) =
      (B * P + A * (1 - P)) / (A + B) := by
    field_simp [hS] <;> ring
  rw [hn, hd, div_div_div_cancel_right₀ hS]

open AddLogReg.Gentle


theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (F : X → ℝ) (x : X) :
    (∀ t : ℝ,
      wCondExpBy ν (logitWeight F)
          (fun x' b => (F x' + (1 / 2) * workingResponse F x' b -
            (F x' + -((2 * ∫ b', (ystar b' - symLogistic (F x)) ∂(ν.condKernel x)) /
              (-4 * ∫ _b', symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x))))) ^ 2) x ≤
        wCondExpBy ν (logitWeight F)
          (fun x' b => (F x' + (1 / 2) * workingResponse F x' b - (F x' + t)) ^ 2) x) ∧
      F x + -((2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
          (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x))) =
        logitBoostStep ν F x := by
  have hw := logit_weight_pos ν F x
  let z : Bool → ℝ := fun b => (1 / 2) * workingResponse F x b
  have hz : (∫ b, z b ∂(ν.condKernel x)) =
      -((2 * ∫ b, (ystar b - symLogistic (F x)) ∂(ν.condKernel x)) /
        (-4 * ∫ _b, symLogistic (F x) * (1 - symLogistic (F x)) ∂(ν.condKernel x))) := by
    dsimp [z, workingResponse]
    rw [integral_const_mul, integral_div, integral_const, probReal_univ, one_smul]
    field_simp
    <;> ring
  constructor
  · intro t
    simp_rw [logit_weighted]
    have h := bool_variance_min (ν.condKernel x) z t
    rw [hz] at h
    convert h using 1 <;> congr 1 <;> ext b <;> dsimp [z] <;> ring
  · unfold logitBoostStep
    rw [logit_weight_cancel]
    ring



#print axioms solution

