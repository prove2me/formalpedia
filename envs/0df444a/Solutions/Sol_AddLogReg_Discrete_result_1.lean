-- Prove2me | solution 1 for AddLogReg.Discrete.result_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:48:49.034044+00:00
-- url     : https://prove2.me/submissions/e93546ca-f68e-4c39-8784-b6508ef3cccd

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AddLogRegR1

lemma int_bool (κ : Measure Bool) [IsFiniteMeasure κ] (h : Bool → ℝ) :
    ∫ b, h b ∂κ = κ.real {true} * h true + κ.real {false} * h false := by
  rw [integral_fintype Integrable.of_finite]
  simp

lemma prob_sum (κ : Measure Bool) [IsProbabilityMeasure κ] :
    κ.real {true} + κ.real {false} = 1 := by
  have h := int_bool κ (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  linarith

lemma part1 (p q a b c s t : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hs : s = 1 ∨ s = -1)
    (ht1 : 0 < (p * (a * 1) + q * (b * -1)) / (p * a + q * b) → t = 1)
    (ht2 : ¬ 0 < (p * (a * 1) + q * (b * -1)) / (p * a + q * b) → t = -1) :
    (p * (a * (1 - 1 * c * t + c ^ 2 / 2)) + q * (b * (1 - -1 * c * t + c ^ 2 / 2))) / (p * a + q * b) ≤
      (p * (a * (1 - 1 * c * s + c ^ 2 / 2)) + q * (b * (1 - -1 * c * s + c ^ 2 / 2))) / (p * a + q * b) := by
  have hD : 0 < p * a + q * b := by
    rcases le_or_gt p 0 with h | h
    · have : q = 1 := by linarith
      subst this; nlinarith
    · nlinarith
  apply div_le_div_of_nonneg_right _ hD.le
  by_cases h : 0 < (p * (a * 1) + q * (b * -1)) / (p * a + q * b)
  · rw [ht1 h]
    have hM : 0 < p * (a * 1) + q * (b * -1) := by
      have := mul_pos h hD; rwa [div_mul_cancel₀ _ hD.ne'] at this
    rcases hs with rfl | rfl <;> nlinarith
  · rw [ht2 h]
    have hM : p * (a * 1) + q * (b * -1) ≤ 0 := by
      have h' : (p * (a * 1) + q * (b * -1)) / (p * a + q * b) ≤ 0 := le_of_not_gt h
      have := mul_le_mul_of_nonneg_right h' hD.le
      rwa [div_mul_cancel₀ _ hD.ne', zero_mul] at this
    rcases hs with rfl | rfl <;> nlinarith

lemma measurable_sgn : Measurable AddLogReg.ExpCrit.sgn := measurable_of_finite _

lemma sgn_cases (b : Bool) : AddLogReg.ExpCrit.sgn b = 1 ∨ AddLogReg.ExpCrit.sgn b = -1 := by
  cases b <;> simp [AddLogReg.ExpCrit.sgn]

lemma exp_pm (c t : ℝ) (ht : t = 1 ∨ t = -1) :
    Real.exp (-(c * t)) = (Real.exp (-c) * (1 + t) + Real.exp c * (1 - t)) / 2 := by
  rcases ht with h | h <;> subst h <;> ring_nf

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

end AddLogRegR1

open AddLogReg.Discrete MeasureTheory ProbabilityTheory in
theorem solution {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) :
    (∀ c : ℝ, 0 < c → ∀ x : X, ∀ s : ℝ, (s = 1 ∨ s = -1) →
      AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * newtonClassifier ν F x + c ^ 2 / 2) x ≤
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 / 2) x) ∧
    (∀ f : X → ℝ, Measurable f → IsPMOne f → 0 < err ν F f → err ν F f < 1 →
      ∀ c' : ℝ, AddLogReg.ExpCrit.J ν (F + lineSearchCoeff (err ν F f) • f) ≤ AddLogReg.ExpCrit.J ν (F + c' • f)) ∧
    (∀ f : X → ℝ, IsPMOne f → ∀ (x : X) (b : Bool),
      Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * Real.exp (-(lineSearchCoeff (err ν F f) * f x * AddLogReg.ExpCrit.sgn b)) =
        Real.exp (-lineSearchCoeff (err ν F f)) * (Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) *
          Real.exp (Real.log ((1 - err ν F f) / err ν F f) * (if AddLogReg.ExpCrit.sgn b ≠ f x then 1 else 0)))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    intro c hc x s hs
    unfold AddLogReg.ExpCrit.wCondExp newtonClassifier AddLogReg.ExpCrit.wCondExp
    simp only [AddLogRegR1.int_bool]
    have hpq := AddLogRegR1.prob_sum (ν.condKernel x)
    have hp : 0 ≤ (ν.condKernel x).real {true} := measureReal_nonneg
    have hq : 0 ≤ (ν.condKernel x).real {false} := measureReal_nonneg
    generalize (ν.condKernel x).real {true} = p at *
    generalize (ν.condKernel x).real {false} = q at *
    simp only [AddLogReg.ExpCrit.sgn]
    exact AddLogRegR1.part1 p q _ _ c s _ hp hq hpq (Real.exp_pos _) (Real.exp_pos _) hc hs
      (fun h => if_pos h) (fun h => if_neg h)
  · -- Part 2
    intro f hfm hf he0 he1 c'
    set w : X × Bool → ℝ := fun z => Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * F z.1)) with hw
    have hsm : Measurable (fun z : X × Bool => AddLogReg.ExpCrit.sgn z.2) :=
      AddLogRegR1.measurable_sgn.comp measurable_snd
    have hwm : Measurable w := by
      rw [hw]
      exact Real.measurable_exp.comp ((hsm.mul (hF.comp measurable_fst)).neg)
    have hwi : Integrable w ν := by
      refine ⟨hwm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le))]
      exact hJ
    have hsf : ∀ z : X × Bool, AddLogReg.ExpCrit.sgn z.2 * f z.1 = 1 ∨
        AddLogReg.ExpCrit.sgn z.2 * f z.1 = -1 := by
      intro z
      rcases AddLogRegR1.sgn_cases z.2 with h1 | h1 <;> rcases hf z.1 with h2 | h2 <;> simp [h1, h2]
    have hui : Integrable (fun z => w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1)) ν := by
      refine hwi.mono (hwm.mul (hsm.mul (hfm.comp measurable_fst))).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rcases hsf z with h | h <;> simp [h]
    set D := ∫ z, w z ∂ν with hD
    set S := ∫ z, w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1) ∂ν with hS
    have hJc : ∀ c'' : ℝ, AddLogReg.ExpCrit.J ν (F + c'' • f) =
        ENNReal.ofReal ((Real.exp (-c'') * (D + S) + Real.exp c'' * (D - S)) / 2) := by
      intro c''
      have hpt : ∀ z : X × Bool, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * (F + c'' • f) z.1)) =
          (Real.exp (-c'') * (w z + w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1)) +
            Real.exp c'' * (w z - w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1))) / 2 := by
        intro z
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
        rw [show -(AddLogReg.ExpCrit.sgn z.2 * (F z.1 + c'' * f z.1)) =
            -(AddLogReg.ExpCrit.sgn z.2 * F z.1) + -(c'' * (AddLogReg.ExpCrit.sgn z.2 * f z.1)) by ring,
          Real.exp_add, AddLogRegR1.exp_pm c'' _ (hsf z)]
        ring
      unfold AddLogReg.ExpCrit.J
      simp_rw [hpt]
      have hint : Integrable (fun z => (Real.exp (-c'') * (w z + w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1)) +
            Real.exp c'' * (w z - w z * (AddLogReg.ExpCrit.sgn z.2 * f z.1))) / 2) ν := by
        exact ((((hwi.add hui).const_mul _).add ((hwi.sub hui).const_mul _)).div_const _)
      rw [← ofReal_integral_eq_lintegral_ofReal hint]
      · congr 1
        rw [integral_div, integral_add, integral_const_mul, integral_const_mul, integral_add hwi hui,
          integral_sub hwi hui]
        · exact (hwi.add hui).const_mul _
        · exact (hwi.sub hui).const_mul _
      · refine Filter.Eventually.of_forall (fun z => ?_)
        have hw0 : 0 < w z := Real.exp_pos _
        rcases hsf z with h | h <;> simp only [h, Pi.zero_apply] <;>
          nlinarith [mul_pos (Real.exp_pos c'') hw0, mul_pos (Real.exp_pos (-c'')) hw0]
    have herr : err ν F f = ((D - S) / 2) / D := by
      unfold err wExp
      beta_reduce
      rw [show (∫ z, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * F z.1)) ∂ν) = D from rfl]
      congr 1
      rw [hD, hS, ← integral_sub hwi hui, ← integral_div]
      congr 1
      ext z
      simp only [hw]
      rcases AddLogRegR1.sgn_cases z.2 with h1 | h1 <;> rcases hf z.1 with h2 | h2 <;> simp [h1, h2] <;>
        (try norm_num)
    -- positivity of A, B
    have hD0 : D ≠ 0 := by
      intro h0; rw [herr, h0, div_zero] at he0; exact lt_irrefl _ he0
    have hDnn : 0 ≤ D := integral_nonneg (fun z => (Real.exp_pos _).le)
    have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hD0)
    have hB : 0 < (D - S) / 2 := by
      rw [herr] at he0; exact (div_pos_iff_of_pos_right hDpos).mp he0
    have hA : 0 < (D + S) / 2 := by
      rw [herr, div_lt_one hDpos] at he1; linarith
    have hratio : (1 - err ν F f) / err ν F f = ((D + S) / 2) / ((D - S) / 2) := by
      rw [herr]; field_simp; ring
    rw [hJc, hJc]
    apply ENNReal.ofReal_le_ofReal
    unfold lineSearchCoeff
    rw [hratio]
    have := AddLogRegR1.real_amgm ((D + S) / 2) ((D - S) / 2) c' hA hB
    linarith
  · -- Part 3
    intro f hf x b
    unfold lineSearchCoeff
    generalize Real.log ((1 - err ν F f) / err ν F f) = L
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rcases AddLogRegR1.sgn_cases b with h1 | h1 <;> rcases hf x with h2 | h2 <;> simp [h1, h2] <;> norm_num <;> ring_nf
