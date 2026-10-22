-- Prove2me | solution 1 for AddLogReg.ExpCrit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:23:37.596972+00:00
-- url     : https://prove2.me/submissions/b7fe47cc-ad54-45fb-8efe-bdc5ca4a8ca9

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AddLogRegL1

lemma measurable_sgn : Measurable AddLogReg.ExpCrit.sgn := measurable_of_finite _

lemma int_bool (κ : Measure Bool) [IsFiniteMeasure κ] (h : Bool → ℝ) :
    ∫ b, h b ∂κ = κ.real {true} * h true + κ.real {false} * h false := by
  rw [integral_fintype Integrable.of_finite]
  simp

lemma prob_sum (κ : Measure Bool) [IsProbabilityMeasure κ] :
    κ.real {true} + κ.real {false} = 1 := by
  have h := int_bool κ (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  linarith

lemma inner (κ : Measure Bool) [IsProbabilityMeasure κ] (t : ℝ) :
    ∫⁻ b, ENNReal.ofReal (Real.exp (-(AddLogReg.ExpCrit.sgn b * t))) ∂κ =
      ENNReal.ofReal (κ.real {true} * Real.exp (-t) + κ.real {false} * Real.exp t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
  rw [int_bool]
  simp [AddLogReg.ExpCrit.sgn]

lemma real_amgm (A B c' : ℝ) (hA : 0 < A) (hB : 0 < B) :
    A * Real.exp (-((1 / 2) * Real.log (A / B))) + B * Real.exp ((1 / 2) * Real.log (A / B)) ≤
      A * Real.exp (-c') + B * Real.exp c' := by
  have hu0 : 0 < Real.exp ((1 / 2) * Real.log (A / B)) := Real.exp_pos _
  have hu2 : Real.exp ((1 / 2) * Real.log (A / B)) ^ 2 = A / B := by
    rw [← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * ((1 / 2) * Real.log (A / B)) = Real.log (A / B) by push_cast; ring]
    exact Real.exp_log (div_pos hA hB)
  have hv0 : 0 < Real.exp c' := Real.exp_pos _
  rw [Real.exp_neg, Real.exp_neg]
  generalize Real.exp ((1 / 2) * Real.log (A / B)) = u at *
  generalize Real.exp c' = v at *
  have hA' : A = B * u ^ 2 := by rw [hu2]; field_simp
  have key : A * v⁻¹ + B * v - (A * u⁻¹ + B * u) = B * (u - v) ^ 2 / v := by
    rw [hA']
    field_simp
    ring
  have : 0 ≤ B * (u - v) ^ 2 / v := by positivity
  linarith

lemma logistic (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A + B = 1) :
    A = Real.exp ((1 / 2) * Real.log (A / B)) /
        (Real.exp (-((1 / 2) * Real.log (A / B))) + Real.exp ((1 / 2) * Real.log (A / B))) ∧
    B = Real.exp (-((1 / 2) * Real.log (A / B))) /
        (Real.exp (-((1 / 2) * Real.log (A / B))) + Real.exp ((1 / 2) * Real.log (A / B))) := by
  have hu0 : 0 < Real.exp ((1 / 2) * Real.log (A / B)) := Real.exp_pos _
  have hu2 : Real.exp ((1 / 2) * Real.log (A / B)) ^ 2 = A / B := by
    rw [← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * ((1 / 2) * Real.log (A / B)) = Real.log (A / B) by push_cast; ring]
    exact Real.exp_log (div_pos hA hB)
  rw [Real.exp_neg]
  generalize Real.exp ((1 / 2) * Real.log (A / B)) = u at *
  have hA' : A = B * u ^ 2 := by rw [hu2]; field_simp
  have hB' : B = 1 / (1 + u ^ 2) := by
    rw [hA'] at hAB
    field_simp
    nlinarith
  have hpos : 0 < 1 + u ^ 2 := by positivity
  constructor
  · rw [hA', hB']
    field_simp
  · rw [hB']
    field_simp

end AddLogRegL1

open AddLogReg.ExpCrit MeasureTheory ProbabilityTheory in
theorem solution {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool)) [IsProbabilityMeasure ν]
    (hη : ∀ᵐ x ∂ν.fst, 0 < condProb ν true x ∧ condProb ν true x < 1) :
    Measurable (halfLogit ν) ∧
    (∀ F : X → ℝ, Measurable F → J ν (halfLogit ν) ≤ J ν F) ∧
    (∀ᵐ x ∂ν.fst,
      condProb ν true x = Real.exp (halfLogit ν x) /
          (Real.exp (-halfLogit ν x) + Real.exp (halfLogit ν x)) ∧
      condProb ν false x = Real.exp (-halfLogit ν x) /
          (Real.exp (-halfLogit ν x) + Real.exp (halfLogit ν x))) := by
  have hmeas : ∀ b : Bool, Measurable (condProb ν b) := fun b =>
    (ν.condKernel.measurable_coe (measurableSet_singleton b)).ennreal_toReal
  have hsum : ∀ x, condProb ν true x + condProb ν false x = 1 := fun x =>
    AddLogRegL1.prob_sum (ν.condKernel x)
  have hH : Measurable (halfLogit ν) := by
    unfold halfLogit
    exact (((hmeas true).div (hmeas false)).log).const_mul _
  have hJeq : ∀ F : X → ℝ, Measurable F → J ν F = ∫⁻ x, ENNReal.ofReal
      (condProb ν true x * Real.exp (-F x) + condProb ν false x * Real.exp (F x)) ∂ν.fst := by
    intro F hF
    unfold J
    have hm : Measurable (fun z : X × Bool =>
        ENNReal.ofReal (Real.exp (-(sgn z.2 * F z.1)))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (((AddLogRegL1.measurable_sgn.comp measurable_snd).mul (hF.comp measurable_fst)).neg))
    rw [← Measure.lintegral_condKernel hm]
    congr 1
    funext x
    exact AddLogRegL1.inner (ν.condKernel x) (F x)
  refine ⟨hH, ?_, ?_⟩
  · intro F hF
    rw [hJeq _ hH, hJeq _ hF]
    apply lintegral_mono_ae
    filter_upwards [hη] with x hx
    apply ENNReal.ofReal_le_ofReal
    have hq : 0 < condProb ν false x := by linarith [hsum x, hx.2]
    exact AddLogRegL1.real_amgm _ _ (F x) hx.1 hq
  · filter_upwards [hη] with x hx
    have hq : 0 < condProb ν false x := by linarith [hsum x, hx.2]
    unfold halfLogit
    exact AddLogRegL1.logistic _ _ hx.1 hq (hsum x)
