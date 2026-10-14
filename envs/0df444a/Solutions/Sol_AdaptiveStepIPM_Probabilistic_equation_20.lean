-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.equation_20
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:32:55.739813+00:00
-- url     : https://prove2.me/submissions/5b659198-33c9-4375-bda9-e34682bfc66b

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

theorem equation_20_core (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin (n - 1))))
        {w | (1 - ε) * Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ ‖w‖}).toReal)
      atTop (nhds 1) := by
  set e := min ε (1 / 4) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  set c := (e ^ 2 - e ^ 3) / 4 with hc
  have hcpos : 0 < c := by
    have : e ^ 3 < e ^ 2 := by
      have : e ^ 3 = e ^ 2 * e := by ring
      rw [this]; nlinarith [pow_pos he0 2]
    rw [hc]; linarith
  have hL : Tendsto (fun n : ℕ => 1 - 2 * Real.exp (-(e ^ 2 - e ^ 3) * ((n - 1 : ℕ) : ℝ) / 4))
      atTop (nhds 1) := by
    have h1 : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => -(e ^ 2 - e ^ 3) * ((n - 1 : ℕ) : ℝ) / 4) atTop atBot := by
      have : Tendsto (fun n : ℕ => c * ((n - 1 : ℕ) : ℝ)) atTop atTop := h1.const_mul_atTop hcpos
      have h3 := tendsto_neg_atTop_atBot.comp this
      refine h3.congr (fun n => ?_)
      simp only [Function.comp, hc]; ring
    have h4 := (Real.tendsto_exp_atBot.comp h2).const_mul 2
    simpa using h4.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds ?_ ?_
  · filter_upwards with n
    set k := n - 1
    have hm := g10_chi_main (stdGaussian (EuclideanSpace ℝ (Fin k))) (fun w => ‖w‖ ^ 2) k
      (g10_chi_norm k) e he0 he1
    refine hm.trans ?_
    rw [← measureReal_def]
    refine measureReal_mono (fun w hw => ?_)
    simp only [Set.mem_setOf_eq] at hw ⊢
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rcases le_or_gt 1 ε with h1 | h1
    · have : (1 - ε) * Real.sqrt k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
      exact this.trans (norm_nonneg _)
    · have hsq : (1 - ε) ^ 2 * (k : ℝ) ≤ ‖w‖ ^ 2 := by
        have : (1 - ε) ^ 2 ≤ 1 - e := by nlinarith
        nlinarith [hw.1]
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith),
        Real.sqrt_sq (norm_nonneg _)] at this
  · filter_upwards with n
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

end AdaptiveStepIPM.Probabilistic

open AdaptiveStepIPM.Probabilistic


theorem solution (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin (n - 1))))
        {w | (1 - ε) * Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ ‖w‖}).toReal)
      atTop (nhds 1) := by
  exact equation_20_core ε hε
