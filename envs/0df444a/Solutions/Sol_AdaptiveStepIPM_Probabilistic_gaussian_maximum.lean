-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.gaussian_maximum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:31:06.494357+00:00
-- url     : https://prove2.me/submissions/d80ea1d6-4e38-4636-9e69-bc6abcb0a3d3

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter


namespace AdaptiveStepIPM.Probabilistic

lemma g10_pdf (x : ℝ) : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal]

lemma g10_int_xexp (t : ℝ) :
    ∫ x in Set.Ioi t, x * Real.exp (-(x ^ 2) / 2) = Real.exp (-(t ^ 2) / 2) := by
  have hderiv : ∀ x ∈ Set.Ici t, HasDerivAt (fun x : ℝ => -Real.exp (-(x ^ 2) / 2))
      (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.neg
    refine this.congr_deriv ?_
    norm_num; ring
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi t) := by
    have := integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
    refine (this.congr ?_).integrableOn
    exact ae_of_all _ (fun x => by simp only; congr 2; ring)
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-(x ^ 2) / 2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
      have : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).atTop_div_const (by norm_num)
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr (fun x => ?_)
      simp [neg_div]
    simpa using (Real.tendsto_exp_atBot.comp h1).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  ring

lemma g10_mills (t : ℝ) (ht : 0 < t) :
    (gaussianReal 0 1).real {x | t ≤ x} ≤
      Real.exp (-(t ^ 2) / 2) / (t * Real.sqrt (2 * Real.pi)) := by
  have hS : {x : ℝ | t ≤ x} = Set.Ici t := rfl
  rw [hS, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici (fun x _ => gaussianPDFReal_nonneg _ _ x)),
    integral_Ici_eq_integral_Ioi]
  have hc : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hint2 : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi t) := by
    have := integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
    refine (this.congr ?_).integrableOn
    exact ae_of_all _ (fun x => by simp only; congr 2; ring)
  calc ∫ x in Set.Ioi t, gaussianPDFReal 0 1 x
      ≤ ∫ x in Set.Ioi t, (t * Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-(x ^ 2) / 2)) := by
        refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (hint2.const_mul _) measurableSet_Ioi (fun x hx => ?_)
        rw [g10_pdf]
        have hx : t < x := hx
        have he := Real.exp_pos (-(x ^ 2) / 2)
        have e : (t * Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-(x ^ 2) / 2)) =
            (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(x ^ 2) / 2) * (x / t)) := by
          field_simp
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
        have : 1 ≤ x / t := by rw [le_div_iff₀ ht]; linarith
        exact le_mul_of_one_le_right he.le this
    _ = Real.exp (-(t ^ 2) / 2) / (t * Real.sqrt (2 * Real.pi)) := by
        rw [integral_const_mul, g10_int_xexp]; ring


lemma g10_mills_lower (t : ℝ) (ht : 0 < t) :
    (gaussianReal 0 1).real {x | x ≤ -t} ≤
      Real.exp (-(t ^ 2) / 2) / (t * Real.sqrt (2 * Real.pi)) := by
  have hpre : {x : ℝ | x ≤ -t} = (fun x : ℝ => -x) ⁻¹' Set.Ici t := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]; constructor <;> intro h <;> linarith
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Ici, gaussianReal_map_neg, neg_zero]
  exact g10_mills t ht

lemma g10_Icc (t : ℝ) (ht : 0 < t) :
    1 - 2 * (Real.exp (-(t ^ 2) / 2) / (t * Real.sqrt (2 * Real.pi))) ≤
      (gaussianReal 0 1).real (Set.Icc (-t) t) := by
  have h1 := g10_mills t ht
  have h2 := g10_mills_lower t ht
  have hc : (Set.Icc (-t) t)ᶜ ⊆ {x | x ≤ -t} ∪ {x | t ≤ x} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · left; exact le_of_lt hx
    · right; exact le_of_lt hx
  have h3 : (gaussianReal 0 1).real (Set.Icc (-t) t)ᶜ ≤
      (gaussianReal 0 1).real {x | x ≤ -t} + (gaussianReal 0 1).real {x | t ≤ x} :=
    (measureReal_mono hc).trans (measureReal_union_le _ _)
  rw [measureReal_compl measurableSet_Icc, probReal_univ] at h3
  linarith

lemma g10_value (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))) {w | supNorm w ≤ t}).toReal =
      ((gaussianReal 0 1).real (Set.Icc (-t) t)) ^ n := by
  have hmeas : MeasurableSet {w : EuclideanSpace ℝ (Fin n) | supNorm w ≤ t} := by
    unfold supNorm
    exact measurableSet_le (continuous_norm.comp
      (EuclideanSpace.equiv (Fin n) ℝ).continuous).measurable measurable_const
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hmeas]
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
      {w | supNorm w ≤ t} = Set.univ.pi (fun _ => Set.Icc (-t) t) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, supNorm, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
    rw [pi_norm_le_iff_of_nonneg ht]
    simp [Real.norm_eq_abs, abs_le]
  rw [hpre, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow]
  rfl

lemma g10_T_atTop : Tendsto (fun n : ℕ => Real.sqrt (2 * Real.log (2 * (n : ℝ)))) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h2 := (Real.tendsto_log_atTop.comp h1).const_mul_atTop (by norm_num : (0:ℝ) < 2)
  exact Real.tendsto_sqrt_atTop.comp h2

theorem gaussian_maximum_core :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin n)))
        {w | supNorm w ≤ Real.sqrt (2 * Real.log (2 * (n : ℝ)))}).toReal)
      atTop (nhds 1) := by
  set T : ℕ → ℝ := fun n => Real.sqrt (2 * Real.log (2 * (n : ℝ))) with hT
  have hc : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hL : Tendsto (fun n : ℕ => 1 - (T n * Real.sqrt (2 * Real.pi))⁻¹) atTop (nhds 1) := by
    have : Tendsto (fun n : ℕ => (T n * Real.sqrt (2 * Real.pi))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (g10_T_atTop.atTop_mul_const hc)
    simpa using this.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
    have hTpos : 0 < T n := Real.sqrt_pos.2 (by linarith)
    rw [g10_value n (T n) hTpos.le]
    have hq := g10_Icc (T n) hTpos
    have hexp : Real.exp (-(T n ^ 2) / 2) = (2 * (n : ℝ))⁻¹ := by
      rw [hT]; simp only
      rw [Real.sq_sqrt (by linarith), show -(2 * Real.log (2 * (n:ℝ))) / 2 = -Real.log (2 * n) by ring,
        Real.exp_neg, Real.exp_log (by linarith)]
    rw [hexp] at hq
    set q := (gaussianReal 0 1).real (Set.Icc (-T n) (T n))
    have hq0 : 0 ≤ q := measureReal_nonneg
    have hb := one_add_mul_le_pow (a := q - 1) (by linarith) n
    rw [add_sub_cancel] at hb
    have key : (n : ℝ) * (1 - q) ≤ (T n * Real.sqrt (2 * Real.pi))⁻¹ := by
      have : 1 - q ≤ 2 * ((2 * (n : ℝ))⁻¹ / (T n * Real.sqrt (2 * Real.pi))) := by linarith
      have e : (n : ℝ) * (2 * ((2 * (n : ℝ))⁻¹ / (T n * Real.sqrt (2 * Real.pi)))) =
          (T n * Real.sqrt (2 * Real.pi))⁻¹ := by
        field_simp
      calc (n : ℝ) * (1 - q) ≤ (n : ℝ) * (2 * ((2 * (n : ℝ))⁻¹ / (T n * Real.sqrt (2 * Real.pi)))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := e
    linarith
  · filter_upwards with n
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

end AdaptiveStepIPM.Probabilistic

open AdaptiveStepIPM.Probabilistic


theorem solution :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin n)))
        {w | supNorm w ≤ Real.sqrt (2 * Real.log (2 * (n : ℝ)))}).toReal)
      atTop (nhds 1) := by
  exact gaussian_maximum_core
