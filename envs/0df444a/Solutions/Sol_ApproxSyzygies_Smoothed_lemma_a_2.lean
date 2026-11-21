-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_a_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:44:22.458124+00:00
-- url     : https://prove2.me/submissions/8403140c-a27c-4bba-bf0f-c713b976f180

import Mathlib

section
open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.A2

lemma coord_int (μ ρ : ℝ) (hρ : 0 < ρ) :
    ∫ x, Real.exp ((x - μ) ^ 2 / (4 * ρ ^ 2)) ∂(gaussianReal μ (ρ ^ 2).toNNReal) = Real.sqrt 2 := by
  have hv : (ρ ^ 2).toNNReal ≠ 0 := by
    simp [Real.toNNReal_eq_zero, hρ.ne']
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hv' : ((ρ ^ 2).toNNReal : ℝ) = ρ ^ 2 := Real.coe_toNNReal _ (by positivity)
  simp only [gaussianPDFReal, smul_eq_mul, hv']
  have h1 : ∀ x : ℝ, (Real.sqrt (2 * Real.pi * ρ ^ 2))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * ρ ^ 2)) *
      Real.exp ((x - μ) ^ 2 / (4 * ρ ^ 2)) =
      (Real.sqrt (2 * Real.pi * ρ ^ 2))⁻¹ * Real.exp (-(1 / (4 * ρ ^ 2)) * (x - μ) ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  have := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (-(1 / (4 * ρ ^ 2)) * y ^ 2)) μ
  rw [this, integral_gaussian]
  have hb : (0 : ℝ) < 4 * ρ ^ 2 := by positivity
  have e1 : Real.pi / (1 / (4 * ρ ^ 2)) = (Real.pi * 4 * ρ ^ 2) := by field_simp
  rw [e1]
  have e2 : Real.pi * 4 * ρ ^ 2 = 2 * (2 * Real.pi * ρ ^ 2) := by ring
  rw [e2, Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num) (2 * Real.pi * ρ ^ 2)]
  have : 0 < Real.sqrt (2 * Real.pi * ρ ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp


lemma tail (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (μ : Fin N → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal)
          {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
        ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 2 - t)) := by
  set P := Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hint1 : ∀ j : Fin N, Integrable (fun x : ℝ => Real.exp ((x - μ j) ^ 2 / (4 * ρ ^ 2)))
      (gaussianReal (μ j) (ρ ^ 2).toNNReal) := by
    intro j
    apply Integrable.of_integral_ne_zero
    rw [coord_int _ _ hρ]
    positivity
  set f : (Fin N → ℝ) → ℝ := fun x => ∏ j, Real.exp ((x j - μ j) ^ 2 / (4 * ρ ^ 2)) with hf
  have hfint : Integrable f P := Integrable.fintype_prod hint1
  have hfint' : ∫ x, f x ∂P = (Real.sqrt 2) ^ N := by
    rw [hf, hP, integral_fintype_prod_eq_prod (fun j (x : ℝ) => Real.exp ((x - μ j) ^ 2 / (4 * ρ ^ 2)))]
    simp [coord_int _ _ hρ]
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := f)
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
    hfint (Real.exp (N + t))
  have hsub : {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖} ⊆
      {x | Real.exp (N + t) ≤ f x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hn : ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖ ^ 2 = ∑ j, (x j - μ j) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have h2 : (2 * ρ * Real.sqrt (N + t)) ^ 2 < ∑ j, (x j - μ j) ^ 2 := by
      rw [← hn]
      exact pow_lt_pow_left₀ hx (by positivity) two_ne_zero
    have h3 : (2 * ρ * Real.sqrt (N + t)) ^ 2 = 4 * ρ ^ 2 * (N + t) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [h3] at h2
    rw [hf]
    simp only
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [← Finset.sum_div, le_div_iff₀ (by positivity)]
    linarith
  have hmono := measure_mono (μ := P) hsub
  have hreal : P.real {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
      ≤ Real.exp (-(N : ℝ) / 2 - t) := by
    have hm2 : P.real {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
        ≤ P.real {x | Real.exp (N + t) ≤ f x} := measureReal_mono hsub
    rw [hfint'] at hmark
    have hpos : 0 < Real.exp ((N : ℝ) + t) := Real.exp_pos _
    have h4 : P.real {x | Real.exp (N + t) ≤ f x} ≤ (Real.sqrt 2) ^ N / Real.exp ((N : ℝ) + t) := by
      rw [le_div_iff₀ hpos]; linarith
    have h5 : (Real.sqrt 2) ^ N ≤ Real.exp ((N : ℝ) / 2) := by
      have : Real.sqrt 2 ≤ Real.exp (1 / 2) := by
        rw [Real.sqrt_le_left (Real.exp_pos _).le]
        rw [← Real.exp_nat_mul]
        have := Real.add_one_le_exp (1 : ℝ)
        norm_num at this ⊢
        linarith
      calc (Real.sqrt 2) ^ N ≤ (Real.exp (1 / 2)) ^ N := pow_le_pow_left₀ (by positivity) this N
        _ = Real.exp ((N : ℝ) / 2) := by rw [← Real.exp_nat_mul]; ring_nf
    calc _ ≤ _ := hm2
      _ ≤ _ := h4
      _ ≤ Real.exp ((N : ℝ) / 2) / Real.exp ((N : ℝ) + t) := by gcongr
      _ = _ := by rw [← Real.exp_sub]; ring_nf
  rw [← ofReal_measureReal (μ := P)]
  exact ENNReal.ofReal_le_ofReal hreal

end ApproxSyzygies.Smoothed.Dev.A2

namespace ApproxSyzygies.Smoothed

theorem chk_lemma_a_2 (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ) (μ : Fin N → ℝ) :
    (∀ t : ℝ, 0 ≤ t →
      (Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal)
          {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
        ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 2 - t))) ∧
    (Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal)
        {x | 2 * ρ * Real.sqrt N < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 2)) := by
  refine ⟨fun t ht => Dev.A2.tail N ρ hρ μ t ht, ?_⟩
  have := Dev.A2.tail N ρ hρ μ 0 le_rfl
  simpa using this

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_a_2 := @ApproxSyzygies.Smoothed.chk_lemma_a_2
