-- Prove2me | solution 1 for AccelScal.UCRace.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:48:38.477855+00:00
-- url     : https://prove2.me/submissions/99894689-52fb-45eb-9f71-93e709770643

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section
open MeasureTheory

namespace AccelScal.UCRace

open ProbabilityTheory Set in
theorem l2_int_exp (a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure a) = ∫ x in Ioi (0:ℝ), a * Real.exp (-(a * x)) * g x := by
  unfold expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 a) (measurable_gammaPDFReal 1 a).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici 0)]
  · rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    rw [gammaPDF_of_nonneg hx', ENNReal.toReal_ofReal]
    · simp
    · simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
      positivity
  · intro x hx
    have : x < 0 := by simpa using hx
    simp [gammaPDF_of_neg this]

open ProbabilityTheory Set in
theorem l2_ae_nonneg (a : ℝ) (ha : 0 < a) : ∀ᵐ x ∂(expMeasure a), 0 ≤ x := by
  rw [ae_iff]
  have : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
  rw [this]
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

open ProbabilityTheory Set in
theorem l2_tail_lt (a : ℝ) (ha : 0 < a) (y : ℝ) (hy : 0 ≤ y) :
    ∫ x in Ioi (0:ℝ), a * Real.exp (-(a * x)) * (if y < x then (1:ℝ) else 0) = Real.exp (-(a * y)) := by
  have h : (fun x : ℝ => a * Real.exp (-(a * x)) * (if y < x then (1:ℝ) else 0))
      = (Ioi y).indicator (fun x => a * Real.exp (-(a * x))) := by
    ext x; by_cases hx : y < x <;> simp [Set.indicator, hx]
  rw [h, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.2 (Ioi_subset_Ioi hy), integral_const_mul]
  have := integral_exp_mul_Ioi (a := -a) (by linarith) y
  simp only [neg_mul] at this
  rw [this]
  field_simp

open ProbabilityTheory Set in
theorem l2_tail_le (a : ℝ) (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    ∫ x in Ioi (0:ℝ), a * Real.exp (-(a * x)) * (if y ≤ x then (1:ℝ) else 0) = Real.exp (-(a * y)) := by
  have h : (fun x : ℝ => a * Real.exp (-(a * x)) * (if y ≤ x then (1:ℝ) else 0))
      = (Ici y).indicator (fun x => a * Real.exp (-(a * x))) := by
    ext x; by_cases hx : y ≤ x <;> simp [Set.indicator, hx]
  rw [h, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Ici_subset_Ioi.2 hy), integral_const_mul, integral_Ici_eq_integral_Ioi]
  have := integral_exp_mul_Ioi (a := -a) (by linarith) y
  simp only [neg_mul] at this
  rw [this]
  field_simp


open ProbabilityTheory Set in
theorem l2_prob (a : ℝ) (ha : 0 < a) : IsProbabilityMeasure (expMeasure a) :=
  isProbabilityMeasure_expMeasure ha

open ProbabilityTheory Set in
theorem l2_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (h : ∀ p : ℝ × ℝ, 0 ≤ p.1 → 0 ≤ p.2 → ‖f p‖ ≤ C) :
    Integrable f ((expMeasure a).prod (expMeasure b)) := by
  have := l2_prob a ha
  have := l2_prob b hb
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  have h1 : ∀ᵐ p : ℝ × ℝ ∂((expMeasure a).prod (expMeasure b)), 0 ≤ p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (l2_ae_nonneg a ha)
  have h2 : ∀ᵐ p : ℝ × ℝ ∂((expMeasure a).prod (expMeasure b)), 0 ≤ p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (l2_ae_nonneg b hb)
  filter_upwards [h1, h2] with p h1 h2 using h p h1 h2

open ProbabilityTheory Set in
theorem l2_E1 (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, Real.exp (-r * p.1) * (if p.1 < p.2 then (1:ℝ) else 0)
      ∂((expMeasure a).prod (expMeasure b)) = a / (a + b + r) := by
  have := l2_prob a ha
  have := l2_prob b hb
  have hint : Integrable (fun p : ℝ × ℝ => Real.exp (-r * p.1) * (if p.1 < p.2 then (1:ℝ) else 0))
      ((expMeasure a).prod (expMeasure b)) := by
    refine l2_integrable a b ha hb _ ?_ 1 ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-r * p.1)).mul
        (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const)
    · intro p h1 h2
      have : Real.exp (-r * p.1) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      split_ifs
      · simpa using this
      · simp
  rw [integral_prod _ hint]
  have e1 : ∀ x : ℝ, ∫ y, Real.exp (-r * x) * (if x < y then (1:ℝ) else 0) ∂(expMeasure b)
      = Real.exp (-r * x) * ∫ y, (if x < y then (1:ℝ) else 0) ∂(expMeasure b) := fun x =>
    integral_const_mul _ _
  simp only [e1]
  rw [l2_int_exp a ha]
  have e2 : ∫ x in Ioi (0:ℝ), a * Real.exp (-(a * x)) *
      (Real.exp (-r * x) * ∫ y, (if x < y then (1:ℝ) else 0) ∂(expMeasure b))
      = ∫ x in Ioi (0:ℝ), a * Real.exp (-((a + b + r) * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    beta_reduce
    rw [l2_int_exp b hb, l2_tail_lt b hb x (le_of_lt hx)]
    have : -((a + b + r) * x) = -(a * x) + -r * x + -(b * x) := by ring
    rw [this, Real.exp_add, Real.exp_add]; ring
  rw [e2, integral_const_mul]
  have := integral_exp_mul_Ioi (a := -(a + b + r)) (by linarith) 0
  simp only [neg_mul, mul_zero, neg_zero, Real.exp_zero] at this
  rw [this]
  field_simp

open ProbabilityTheory Set in
theorem l2_E2 (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, Real.exp (-r * p.2) * (if p.2 ≤ p.1 then (1:ℝ) else 0)
      ∂((expMeasure a).prod (expMeasure b)) = b / (a + b + r) := by
  have := l2_prob a ha
  have := l2_prob b hb
  have hint : Integrable (fun p : ℝ × ℝ => Real.exp (-r * p.2) * (if p.2 ≤ p.1 then (1:ℝ) else 0))
      ((expMeasure a).prod (expMeasure b)) := by
    refine l2_integrable a b ha hb _ ?_ 1 ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-r * p.2)).mul
        (Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const measurable_const)
    · intro p h1 h2
      have : Real.exp (-r * p.2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      split_ifs
      · simpa using this
      · simp
  rw [integral_prod_symm _ hint]
  have e1 : ∀ y : ℝ, ∫ x, Real.exp (-r * y) * (if y ≤ x then (1:ℝ) else 0) ∂(expMeasure a)
      = Real.exp (-r * y) * ∫ x, (if y ≤ x then (1:ℝ) else 0) ∂(expMeasure a) := fun y =>
    integral_const_mul _ _
  simp only [e1]
  rw [l2_int_exp b hb]
  have e2 : ∫ y in Ioi (0:ℝ), b * Real.exp (-(b * y)) *
      (Real.exp (-r * y) * ∫ x, (if y ≤ x then (1:ℝ) else 0) ∂(expMeasure a))
      = ∫ y in Ioi (0:ℝ), b * Real.exp (-((a + b + r) * y)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    beta_reduce
    rw [l2_int_exp a ha, l2_tail_le a ha y hy]
    have : -((a + b + r) * y) = -(b * y) + -r * y + -(a * y) := by ring
    rw [this, Real.exp_add, Real.exp_add]; ring
  rw [e2, integral_const_mul]
  have := integral_exp_mul_Ioi (a := -(a + b + r)) (by linarith) 0
  simp only [neg_mul, mul_zero, neg_zero, Real.exp_zero] at this
  rw [this]
  field_simp


theorem l2_intexp (r m : ℝ) (hr : 0 < r) :
    ∫ t in (0:ℝ)..m, Real.exp (-r * t) = (1 - Real.exp (-r * m)) / r := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) m, HasDerivAt (fun t => -(Real.exp (-r * t)) / r)
      (Real.exp (-r * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -r * t) (-r) x := by
      simpa using (hasDerivAt_id x).const_mul (-r)
    have h2 := (h1.exp).neg.div_const r
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

open ProbabilityTheory Set in
theorem l2_gen (a b r u R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, (Real.exp (-r * p.1) * u * (if p.1 < p.2 then 1 else 0)
      - R * ∫ t in (0:ℝ)..(min p.1 p.2), Real.exp (-r * t))
      ∂((expMeasure a).prod (expMeasure b)) = (u * a - R) / (r + a + b) := by
  have := l2_prob a ha
  have := l2_prob b hb
  set G1 : ℝ × ℝ → ℝ := fun p => Real.exp (-r * p.1) * (if p.1 < p.2 then (1:ℝ) else 0) with hG1
  set G2 : ℝ × ℝ → ℝ := fun p => Real.exp (-r * p.2) * (if p.2 ≤ p.1 then (1:ℝ) else 0) with hG2
  have i1 : Integrable G1 ((expMeasure a).prod (expMeasure b)) := by
    refine l2_integrable a b ha hb _ ?_ 1 ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-r * p.1)).mul
        (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const)
    · intro p h1 h2
      have : Real.exp (-r * p.1) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [hG1]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      split_ifs
      · simpa using this
      · simp
  have i2 : Integrable G2 ((expMeasure a).prod (expMeasure b)) := by
    refine l2_integrable a b ha hb _ ?_ 1 ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-r * p.2)).mul
        (Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const measurable_const)
    · intro p h1 h2
      have : Real.exp (-r * p.2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [hG2]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      split_ifs
      · simpa using this
      · simp
  have hpt : ∀ p : ℝ × ℝ, (Real.exp (-r * p.1) * u * (if p.1 < p.2 then 1 else 0)
      - R * ∫ t in (0:ℝ)..(min p.1 p.2), Real.exp (-r * t)) =
      u * G1 p - (R / r) * (1 - (G1 p + G2 p)) := by
    intro p
    rw [l2_intexp r _ hr]
    simp only [hG1, hG2]
    by_cases h : p.1 < p.2
    · have : min p.1 p.2 = p.1 := min_eq_left h.le
      rw [this, if_pos h, if_neg (not_le.2 h)]
      field_simp
      ring
    · have : min p.1 p.2 = p.2 := min_eq_right (not_lt.1 h)
      rw [this, if_neg h, if_pos (not_lt.1 h)]
      field_simp
      ring
  simp_rw [hpt]
  have iG : Integrable (fun p => G1 p + G2 p) ((expMeasure a).prod (expMeasure b)) := i1.add i2
  have iH : Integrable (fun p : ℝ × ℝ => R / r * (1 - (G1 p + G2 p)))
      ((expMeasure a).prod (expMeasure b)) := ((integrable_const (1:ℝ)).sub iG).const_mul _
  rw [integral_sub (i1.const_mul u) iH]
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_const (1:ℝ)) iG,
    integral_add i1 i2]
  have e1 : ∫ p, G1 p ∂((expMeasure a).prod (expMeasure b)) = a / (a + b + r) := l2_E1 a b r ha hb hr
  have e2 : ∫ p, G2 p ∂((expMeasure a).prod (expMeasure b)) = b / (a + b + r) := l2_E2 a b r ha hb hr
  rw [e1, e2]
  simp
  field_simp
  ring

theorem lemma_2_core (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    payoff1 T1 T2 r R1 R2 = V1 T1 T2 r R1 R2 ∧
      payoff2 T1 T2 r R1 R2 =
        (T2.u R2 * T2.lam R2 - R2) / (r + T1.lam R1 + T2.lam R2) := by
  obtain ⟨hA1, hη1, -, -, -, -, -, -⟩ := h1
  obtain ⟨hA2, hη2, -, -, -, -, -, -⟩ := h2
  have hl1 : 0 < T1.lam R1 := mul_pos hη1 (Real.rpow_pos_of_pos hR1 _)
  have hl2 : 0 < T2.lam R2 := mul_pos hη2 (Real.rpow_pos_of_pos hR2 _)
  have := l2_prob _ hl1
  have := l2_prob _ hl2
  constructor
  · unfold payoff1 V1 exponentialRace
    exact l2_gen _ _ r _ _ hl1 hl2 hr
  · unfold payoff2 exponentialRace
    have := l2_gen (T2.lam R2) (T1.lam R1) r (T2.u R2) R2 hl2 hl1 hr
    rw [← integral_prod_swap (μ := ProbabilityTheory.expMeasure (T2.lam R2))
      (ν := ProbabilityTheory.expMeasure (T1.lam R1))] at this
    have e : (r + T2.lam R2 + T1.lam R1) = (r + T1.lam R1 + T2.lam R2) := by ring
    rw [e] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap, min_comm p.2 p.1]

end AccelScal.UCRace

open AccelScal.UCRace


theorem solution (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    payoff1 T1 T2 r R1 R2 = V1 T1 T2 r R1 R2 ∧
      payoff2 T1 T2 r R1 R2 =
        (T2.u R2 * T2.lam R2 - R2) / (r + T1.lam R1 + T2.lam R2) := by
  exact lemma_2_core T1 T2 h1 h2 r hr R1 R2 hR1 hR2
