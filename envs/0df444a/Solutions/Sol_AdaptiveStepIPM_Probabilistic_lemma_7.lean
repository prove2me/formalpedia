-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:37:25.213986+00:00
-- url     : https://prove2.me/submissions/a6f65fa5-702d-491b-b712-aae4b2a241a6

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter


namespace AdaptiveStepIPM.Probabilistic

def G10ChiMGF {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    (Q : Ω → ℝ) (k : ℕ) : Prop :=
  ∀ lam : ℝ, lam < 1 / 2 → ∫ ω, Real.exp (lam * Q ω) ∂Prob = (1 - 2 * lam) ^ (-(k : ℝ) / 2)

lemma g10_log_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |(-ε)| < 1 := by rw [abs_neg, abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [abs_neg, abs_of_pos h0, sub_neg_eq_add] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  have e3 : (-ε) ^ 3 = -ε ^ 3 := by ring
  have e4 : (-ε) ^ 4 = ε ^ 4 := by ring
  have e5 : (-ε) ^ 5 = -ε ^ 5 := by ring
  have e6 : (-ε) ^ 6 = ε ^ 6 := by ring
  rw [e3, e4, e5, e6] at h'
  norm_num at h'
  have hd : ε ^ 7 / (1 - ε) ≤ 2 * ε ^ 7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 7) h0]
  have p : ε ^ 7 ≤ ε ^ 3 / 16 := by
    have : ε ^ 4 ≤ (1/2) ^ 4 := pow_le_pow_left₀ h0.le h1.le 4
    nlinarith [pow_pos h0 3]
  have q : ε ^ 5 ≤ ε ^ 3 / 4 := by
    have : ε ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
    nlinarith [pow_pos h0 3]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 6]

lemma g10_log_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |ε| < 1 := by rw [abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [abs_of_pos h0] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  norm_num at h'
  have hd : ε ^ 5 / (1 - ε) ≤ 2 * ε ^ 5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 5) h0]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, mul_pos (pow_pos h0 3) h0,
    mul_pos (pow_pos h0 3) (pow_pos h0 2)]

lemma g10_chi_integrable {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} {Q : Ω → ℝ} {k : ℕ}
    (hQ : G10ChiMGF Prob Q k) {lam : ℝ} (hl : lam < 1 / 2) :
    Integrable (fun ω => Real.exp (lam * Q ω)) Prob := by
  by_contra hni
  have := hQ lam hl
  rw [integral_undef hni] at this
  have hpos : 0 < (1 - 2 * lam) ^ (-(k : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  linarith

theorem g10_chi_main {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : G10ChiMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set B := Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) with hB
  -- upper tail
  set t := ε / (2 * (1 + ε)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t < 1 / 2 := by rw [ht, div_lt_iff₀ (by positivity)]; linarith
  have hup := measure_ge_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 + ε) * k) ht0
    (g10_chi_integrable hQ htl)
  have hmgf1 : mgf Q Prob t = (1 - 2 * t) ^ (-(k : ℝ) / 2) := hQ t htl
  have h12t : 1 - 2 * t = (1 + ε)⁻¹ := by rw [ht]; field_simp <;> ring
  have hupB : Prob.real {ω | (1 + ε) * k ≤ Q ω} ≤ B := by
    refine hup.trans (le_of_eq_of_le (by rw [hmgf1]) ?_)
    rw [h12t, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := g10_log_upper hε0 hε1
    have : -t * ((1 + ε) * k) = -(ε * k / 2) := by rw [ht]; field_simp <;> ring
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 + ε))]
  -- lower tail
  set s := -(ε / (2 * (1 - ε))) with hs
  have h1e' : (0 : ℝ) < 1 - ε := by linarith
  have hs0 : s ≤ 0 := by rw [hs]; exact neg_nonpos.mpr (by positivity)
  have hsl : s < 1 / 2 := by linarith
  have hlo := measure_le_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 - ε) * k) hs0
    (g10_chi_integrable hQ hsl)
  have hmgf2 : mgf Q Prob s = (1 - 2 * s) ^ (-(k : ℝ) / 2) := hQ s hsl
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have h12s : 1 - 2 * s = (1 - ε)⁻¹ := by rw [hs]; field_simp <;> ring
  have hloB : Prob.real {ω | Q ω ≤ (1 - ε) * k} ≤ B := by
    refine hlo.trans (le_of_eq_of_le (by rw [hmgf2]) ?_)
    rw [h12s, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := g10_log_lower hε0 hε1
    have : -s * ((1 - ε) * k) = ε * k / 2 := by rw [hs]; field_simp
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 - ε))]
  -- combine
  set E := {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)}
  have hsub : Eᶜ ⊆ {ω | (1 + ε) * k ≤ Q ω} ∪ {ω | Q ω ≤ (1 - ε) * k} := by
    intro ω hω
    simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · right; exact h.le
    · left; exact h.le
  have h1 : (1 : ℝ) ≤ Prob.real E + Prob.real Eᶜ := by
    have := measureReal_union_le (μ := Prob) E Eᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  have h2 := (measureReal_mono (μ := Prob) hsub).trans (measureReal_union_le _ _)
  linarith


lemma g10_sq_mgf {lam : ℝ} (hl : lam < 1 / 2) :
    ∫ x, Real.exp (lam * x ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * lam) ^ (-(1 : ℝ) / 2) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hb : 0 < 1 / 2 - lam := by linarith
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (lam * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - lam) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  simp_rw [e]
  rw [integral_const_mul, integral_gaussian]
  have e1 : Real.pi / (1 / 2 - lam) = (2 * Real.pi) / (1 - 2 * lam) := by
    field_simp <;> ring
  have h2 : 0 < 1 - 2 * lam := by linarith
  rw [e1, Real.sqrt_div (by positivity), show -(1 : ℝ) / 2 = -(1 / 2) by ring,
    Real.rpow_neg h2.le, ← Real.sqrt_eq_rpow]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma g10_chi_norm (k : ℕ) :
    G10ChiMGF (stdGaussian (EuclideanSpace ℝ (Fin k))) (fun w => ‖w‖ ^ 2) k := by
  intro lam hl
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  have h3 : ∀ x : Fin k → ℝ, Real.exp (lam * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2) =
      ∏ i, Real.exp (lam * (x i) ^ 2) := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [h3]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin k) (y : ℝ) => Real.exp (lam * y ^ 2))]
  simp_rw [g10_sq_mgf hl]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
    ← Real.rpow_mul (by linarith)]
  congr 1
  ring

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

lemma g10_abs_tail (a : ℝ) (ha : 0 < a) :
    (gaussianReal 0 1).real {y | a < |y|} ≤
      2 * (Real.exp (-(a ^ 2) / 2) / (a * Real.sqrt (2 * Real.pi))) := by
  have hc : {y : ℝ | a < |y|} ⊆ {x | x ≤ -a} ∪ {x | a ≤ x} := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rcases le_or_gt 0 y with h | h
    · right; rw [abs_of_nonneg h] at hy; exact hy.le
    · left; rw [abs_of_neg h] at hy; show y ≤ -a; linarith
  have h3 := (measureReal_mono (μ := gaussianReal 0 1) hc).trans (measureReal_union_le _ _)
  linarith [g10_mills a ha, g10_mills_lower a ha]

lemma g10_coord_tail {k n : ℕ}
    (H : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (j : Fin n) (a : ℝ) (ha : 0 < a) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).real {w | a < |(H w) j|} ≤
      2 * (Real.exp (-(a ^ 2) / 2) / (a * Real.sqrt (2 * Real.pi))) := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).comp H.toContinuousLinearMap with hLdef
  have hL : ∀ w, L w = (H w) j := fun w => rfl
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
    rw [hL, one_mul]
    exact (PiLp.norm_apply_le (H w) j).trans (H.norm_map w).le
  have hmeasS : MeasurableSet {y : ℝ | a < |y|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hset : {w | a < |(H w) j|} = L ⁻¹' {y : ℝ | a < |y|} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_preimage, hL]
  rw [hset, ← map_measureReal_apply L.continuous.measurable hmeasS,
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  set s := ‖L‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hmap : gaussianReal 0 (s ^ 2).toNNReal = (gaussianReal 0 1).map (fun y => s * y) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [Real.coe_toNNReal _ (sq_nonneg s)]
  rw [hmap, map_measureReal_apply (by fun_prop) hmeasS]
  refine le_trans (measureReal_mono (fun y hy => ?_)) (g10_abs_tail a ha)
  simp only [Set.mem_preimage, Set.mem_setOf_eq, abs_mul, abs_of_nonneg hs0] at hy ⊢
  nlinarith [abs_nonneg y]

lemma g10_log_ge (n : ℕ) (hn : 100 ≤ n) : 4 ≤ Real.log n := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [pow_le_pow_left₀ h0.le h1.le 4]

lemma g10_key_ineq (n : ℕ) (hn : 100 ≤ n) (Q : ℝ) (hQ : 9 / 10 * ((n : ℝ) - 1) ≤ Q) :
    2 * Real.log (2 * (n : ℝ)) ≤ 3 * Real.log n / n * Q := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := g10_log_ge n hn
  have hl2 := Real.log_two_lt_d9
  rw [Real.log_mul (by norm_num) (by linarith)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hQ (by linarith : (0:ℝ) ≤ 3 * Real.log n)]

theorem lemma_7_core (F : ∀ n : ℕ, 2 ≤ n → Frame n) :
    Tendsto (fun n : ℕ =>
      if hn : 2 ≤ n then
        ((sphereGaussian (n - 1))
          {v | supNorm ((F n hn).H v) ≤
            Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal
      else 1) atTop (nhds 1) := by
  set a : ℕ → ℝ := fun n => Real.sqrt (2 * Real.log (2 * (n : ℝ))) with ha
  set e : ℝ := 1 / 10 with he
  have hc : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hU : Tendsto (fun n : ℕ => 1 - ((a n * Real.sqrt (2 * Real.pi))⁻¹ +
      2 * Real.exp (-(e ^ 2 - e ^ 3) * ((n - 1 : ℕ) : ℝ) / 4))) atTop (nhds 1) := by
    have h0 : Tendsto (fun n : ℕ => (a n * Real.sqrt (2 * Real.pi))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (g10_T_atTop.atTop_mul_const hc)
    have h1 : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => -(e ^ 2 - e ^ 3) * ((n - 1 : ℕ) : ℝ) / 4) atTop atBot := by
      have : Tendsto (fun n : ℕ => (e ^ 2 - e ^ 3) / 4 * ((n - 1 : ℕ) : ℝ)) atTop atTop :=
        h1.const_mul_atTop (by norm_num [he])
      have h3 := tendsto_neg_atTop_atBot.comp this
      refine h3.congr (fun n => ?_)
      simp only [Function.comp]; ring
    have h4 := (Real.tendsto_exp_atBot.comp h2).const_mul 2
    have h5 := (h0.add h4).const_sub 1
    simpa using h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hU tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 100] with n hn
    have h2n : 2 ≤ n := by omega
    rw [dif_pos h2n]
    generalize (F n h2n).H = H
    revert H
    generalize hk : n - 1 = k
    intro H
    set μ := stdGaussian (EuclideanSpace ℝ (Fin k))
    set s := Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ)) with hs
    set S := {v : EuclideanSpace ℝ (Fin k) | supNorm (H v) ≤ s}
    set f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun w => (‖w‖⁻¹) • w
    have hf : Measurable f := by fun_prop
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
    have hkR : ((k : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [← hk, Nat.cast_sub (by omega)]; simp
    have hlog : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
    have hapos : 0 < a n := Real.sqrt_pos.2 (by linarith)
    -- reduce to the Gaussian
    have hmapS : (μ (f ⁻¹' S)).toReal ≤ ((sphereGaussian k) S).toReal := by
      refine ENNReal.toReal_mono ?_ (Measure.le_map_apply hf.aemeasurable S)
      haveI : IsProbabilityMeasure (sphereGaussian k) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
      exact measure_ne_top _ _
    refine le_trans ?_ hmapS
    rw [← measureReal_def]
    -- events
    set A : Fin n → Set (EuclideanSpace ℝ (Fin k)) := fun j => {w | a n < |(H w) j|}
    set D := {w : EuclideanSpace ℝ (Fin k) | (1 - e) * (k : ℝ) ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ (1 + e) * (k : ℝ)}
    have hDm : MeasurableSet D := by
      exact (measurableSet_le measurable_const (continuous_norm.pow 2).measurable).inter
        (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)
    have hD := g10_chi_main μ (fun w => ‖w‖ ^ 2) k (g10_chi_norm k) e (by norm_num [he]) (by norm_num [he])
    have hDc : μ.real Dᶜ ≤ 2 * Real.exp (-(e ^ 2 - e ^ 3) * k / 4) := by
      have hD' : 1 - 2 * Real.exp (-(e ^ 2 - e ^ 3) * k / 4) ≤ μ.real D := hD
      rw [measureReal_compl hDm, probReal_univ]; linarith
    have hA : ∀ j, μ.real (A j) ≤ 2 * (Real.exp (-(a n ^ 2) / 2) / (a n * Real.sqrt (2 * Real.pi))) :=
      fun j => g10_coord_tail H j (a n) hapos
    have hexp : Real.exp (-(a n ^ 2) / 2) = (2 * (n : ℝ))⁻¹ := by
      rw [ha]; simp only
      rw [Real.sq_sqrt (by linarith), show -(2 * Real.log (2 * (n:ℝ))) / 2 = -Real.log (2 * n) by ring,
        Real.exp_neg, Real.exp_log (by linarith)]
    have hsumA : μ.real (⋃ j, A j) ≤ (a n * Real.sqrt (2 * Real.pi))⁻¹ := by
      refine (measureReal_iUnion_fintype_le _).trans ?_
      refine (Finset.sum_le_sum (fun j _ => hA j)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hexp]
      field_simp
    -- inclusion
    have hsub : (f ⁻¹' S)ᶜ ⊆ (⋃ j, A j) ∪ Dᶜ := by
      intro w hw
      by_contra hcon
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists, not_not] at hcon
      obtain ⟨hAj, hwD⟩ := hcon
      apply hw
      have hQ : (1 - e) * (k : ℝ) ≤ ‖w‖ ^ 2 := hwD.1
      rw [hkR] at hQ
      have hwpos : 0 < ‖w‖ := by
        have : 0 < ‖w‖ ^ 2 := by
          have : (0:ℝ) < (1 - e) * ((n : ℝ) - 1) := by rw [he]; nlinarith
          linarith
        rcases (norm_nonneg w).eq_or_lt with h | h
        · rw [← h] at this; simp at this
        · exact h
      have hcoord : ∀ j, |(H w) j| ≤ a n := fun j => not_lt.1 (hAj j)
      have has : a n ≤ s * ‖w‖ := by
        have hineq : 2 * Real.log (2 * (n : ℝ)) ≤ (s * ‖w‖) ^ 2 := by
          rw [mul_pow, hs, Real.sq_sqrt (by
            have := g10_log_ge n hn; positivity)]
          exact g10_key_ineq n hn _ (by rw [he] at hQ; linarith)
        have := Real.sqrt_le_sqrt hineq
        rwa [Real.sqrt_sq (by positivity)] at this
      show supNorm (H (f w)) ≤ s
      unfold supNorm
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      refine (pi_norm_le_iff_of_nonneg hs0).2 (fun j => ?_)
      simp only [f, LinearIsometry.map_smul]
      rw [Real.norm_eq_abs]
      simp only [EuclideanSpace.equiv, PiLp.smul_apply]
      change |(‖w‖⁻¹ • H w) j| ≤ s
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm, inv_mul_le_iff₀ hwpos]
      linarith [hcoord j, mul_comm s ‖w‖]
    have h1 : (1 : ℝ) ≤ μ.real (f ⁻¹' S) + μ.real (f ⁻¹' S)ᶜ := by
      have := measureReal_union_le (μ := μ) (f ⁻¹' S) (f ⁻¹' S)ᶜ
      rwa [Set.union_compl_self, probReal_univ] at this
    have h2 := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    linarith
  · filter_upwards with n
    split_ifs with h
    · haveI : IsProbabilityMeasure (sphereGaussian (n - 1)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    · exact le_rfl

end AdaptiveStepIPM.Probabilistic

open AdaptiveStepIPM.Probabilistic


theorem solution (F : ∀ n : ℕ, 2 ≤ n → Frame n) :
    Tendsto (fun n : ℕ =>
      if hn : 2 ≤ n then
        ((sphereGaussian (n - 1))
          {v | supNorm ((F n hn).H v) ≤
            Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal
      else 1) atTop (nhds 1) := by
  exact lemma_7_core F
