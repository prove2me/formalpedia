-- Prove2me | solution 1 for AuctionDuration.ClearingError.lemma_A_2_eq_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:24:05.506205+00:00
-- url     : https://prove2.me/submissions/e9beea4a-6b1c-4191-b9b5-e64bee03a46d

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

namespace ADSeries

theorem hasSum_exp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

/-- termwise integration of a power series with nonnegative coefficients on `[0, m]`. -/
theorem hasSum_integral (m : ℝ) (hm : 0 ≤ m) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable (fun n => c n * m ^ n)) (f : ℝ → ℝ)
    (hf : ∀ s ∈ Set.Ioc 0 m, HasSum (fun n => c n * s ^ n) (f s)) :
    HasSum (fun n => c n * (m ^ (n + 1) / (n + 1))) (∫ s in (0 : ℝ)..m, f s) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := m) (F := fun n s => c n * s ^ n) (f := f)
    (fun n _ => c n * m ^ n)
    (fun n => (by fun_prop : Continuous fun s : ℝ => c n * s ^ n).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun t ht => by
      rw [Set.uIoc_of_le hm] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc n) (pow_nonneg ht.1.le n))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2 n) (hc n)))
    (ae_of_all _ (fun t _ => hsum))
    intervalIntegrable_const
    (ae_of_all _ (fun t ht => by
      rw [Set.uIoc_of_le hm] at ht
      exact hf t ht))
  have e : (fun n => ∫ t in (0 : ℝ)..m, c n * t ^ n) = fun n => c n * (m ^ (n + 1) / (n + 1)) := by
    funext n
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
  rw [e] at key
  exact key

theorem summable_aux (m : ℝ) (hm : 0 ≤ m) :
    Summable (fun n : ℕ => 1 / ((n + 1)! : ℝ) * m ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial m)
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.factorial_le (Nat.le_succ n)

/-- `∫_0^m (e^s-1)/s ds = ∑ m^{n+1}/((n+1) (n+1)!)`. -/
theorem hasSum_I1 (m : ℝ) (hm : 0 ≤ m) :
    HasSum (fun n : ℕ => 1 / ((n + 1)! : ℝ) * (m ^ (n + 1) / (n + 1)))
      (∫ s in (0 : ℝ)..m, (Real.exp s - 1) / s) := by
  apply hasSum_integral m hm _ (fun n => by positivity) (summable_aux m hm)
  intro s hs
  have h1 := (hasSum_nat_add_iff' 1).mpr (hasSum_exp s)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h1
  have h2 := h1.div_const s
  have : s ≠ 0 := hs.1.ne'
  have e : (fun n : ℕ => s ^ (n + 1) / ((n + 1)! : ℝ) / s) = fun n => 1 / ((n + 1)! : ℝ) * s ^ n := by
    funext n
    rw [pow_succ]
    field_simp
  rw [e] at h2
  exact h2

/-- `∫_0^m (1/s) ∫_0^s (e^u-1)/u du ds = ∑ m^{n+1}/((n+1)^2 (n+1)!)`. -/
theorem hasSum_I2 (m : ℝ) (hm : 0 ≤ m) :
    HasSum (fun n : ℕ => 1 / ((n + 1)! : ℝ) / (n + 1) * (m ^ (n + 1) / (n + 1)))
      (∫ s in (0 : ℝ)..m, (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u) := by
  apply hasSum_integral m hm _ (fun n => by positivity)
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_aux m hm)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_self (by positivity)
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · intro s hs
    have h := (hasSum_I1 s hs.1.le).mul_left (1 / s)
    have : s ≠ 0 := hs.1.ne'
    have e : (fun n : ℕ => 1 / s * (1 / ((n + 1)! : ℝ) * (s ^ (n + 1) / (n + 1)))) =
        fun n => 1 / ((n + 1)! : ℝ) / (n + 1) * s ^ n := by
      funext n
      rw [pow_succ]
      field_simp
    rw [e] at h
    exact h

end ADSeries

namespace ADSeries

theorem int_poisson {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (m : ℝ≥0) (hlaw : P.map N = poissonMeasure m) (F : ℕ → ℝ) :
    ∫ ω, F (N ω) ∂P = ∑' n, Real.exp (-(m : ℝ)) * (m : ℝ) ^ n / (n ! : ℝ) * F n := by
  rw [← integral_map hN.aemeasurable .of_discrete, hlaw, integral_poissonMeasure]
  simp [smul_eq_mul]

end ADSeries

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (m : ℝ≥0) (hm : 0 < m) (hlaw : P.map N = poissonMeasure m) :
    ∫ ω, 1 / (1 + (N ω : ℝ)) ^ 2 ∂P =
        Real.exp (-(m : ℝ)) / (m : ℝ) * ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s ∧
    ∫ ω, 1 / (2 + (N ω : ℝ)) ^ 2 ∂P =
        1 / (m : ℝ) ^ 2 * (1 - Real.exp (-(m : ℝ)) -
          Real.exp (-(m : ℝ)) * ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s) := by
  have hm' : (m : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hm).ne'
  constructor
  · refine (ADSeries.int_poisson P N hN m hlaw (fun n => 1 / (1 + (n : ℝ)) ^ 2)).trans ?_
    have hg := (ADSeries.hasSum_I1 (m : ℝ) m.2).mul_left (Real.exp (-(m : ℝ)) / (m : ℝ))
    have e : (fun n : ℕ => Real.exp (-(m : ℝ)) / (m : ℝ) *
        (1 / ((n + 1)! : ℝ) * ((m : ℝ) ^ (n + 1) / (n + 1)))) =
        fun n => Real.exp (-(m : ℝ)) * (m : ℝ) ^ n / (n ! : ℝ) * (1 / (1 + (n : ℝ)) ^ 2) := by
      funext n
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring
    rw [e] at hg
    exact hg.tsum_eq
  · refine (ADSeries.int_poisson P N hN m hlaw (fun n => 1 / (2 + (n : ℝ)) ^ 2)).trans ?_
    set I := ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s with hI
    have h1 := (hasSum_nat_add_iff' 1).mpr (ADSeries.hasSum_exp (m : ℝ))
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one] at h1
    have h2 := h1.sub (ADSeries.hasSum_I1 (m : ℝ) m.2)
    set g : ℕ → ℝ := fun n => (m : ℝ) ^ (n + 1) / ((n + 1)! : ℝ) -
      1 / ((n + 1)! : ℝ) * ((m : ℝ) ^ (n + 1) / (n + 1)) with hgdef
    have h3 := (hasSum_nat_add_iff' 1).mpr h2
    rw [Finset.sum_range_one] at h3
    have g0 : g 0 = 0 := by simp [hgdef]
    rw [g0, sub_zero] at h3
    have h4 := h3.mul_left (Real.exp (-(m : ℝ)) / (m : ℝ) ^ 2)
    have e : (fun n : ℕ => Real.exp (-(m : ℝ)) / (m : ℝ) ^ 2 *
        ((m : ℝ) ^ (n + 1 + 1) / ((n + 1 + 1)! : ℝ) -
          1 / ((n + 1 + 1)! : ℝ) * ((m : ℝ) ^ (n + 1 + 1) / ((n + 1 : ℕ) + 1)))) =
        fun n => Real.exp (-(m : ℝ)) * (m : ℝ) ^ n / (n ! : ℝ) * (1 / (2 + (n : ℝ)) ^ 2) := by
      funext n
      rw [Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
      push_cast
      field_simp
      ring
    rw [e] at h4
    rw [h4.tsum_eq]
    have hexp : Real.exp (-(m : ℝ)) * Real.exp (m : ℝ) = 1 := by
      rw [← Real.exp_add]; simp
    have hr : ∀ J : ℝ, Real.exp (-(m : ℝ)) / (m : ℝ) ^ 2 * (Real.exp (m : ℝ) - 1 - J) =
        1 / (m : ℝ) ^ 2 * (Real.exp (-(m : ℝ)) * Real.exp (m : ℝ) - Real.exp (-(m : ℝ)) -
          Real.exp (-(m : ℝ)) * J) := fun J => by ring
    rw [hr, hexp]


