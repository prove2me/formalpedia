-- Prove2me | solution 1 for AgrawalGoyalTS.TwoArmed.beta_cdf_eq_one_sub_binom_cdf
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:16:31.495612+00:00
-- url     : https://prove2.me/submissions/65c494c3-7d79-40d2-8c91-87609b650e91

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Polynomial

namespace AGTAux

noncomputable def Pfun (j s : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1), (bernsteinPolynomial ℝ (j + 1) k).eval y

lemma deriv_partial (j : ℕ) : ∀ s : ℕ,
    Polynomial.derivative (∑ k ∈ Finset.range (s + 1), bernsteinPolynomial ℝ (j + 1) k) =
      -((j + 1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ j s := by
  intro s
  induction s with
  | zero =>
    simp [bernsteinPolynomial.derivative_zero]
  | succ s ih =>
    rw [Finset.sum_range_succ, derivative_add, ih, bernsteinPolynomial.derivative_succ]
    simp only [Nat.add_sub_cancel]
    ring

lemma hasDerivAt_Pfun (j s : ℕ) (y : ℝ) :
    HasDerivAt (Pfun j s) (-((j : ℝ) + 1) * (bernsteinPolynomial ℝ j s).eval y) y := by
  have h := Polynomial.hasDerivAt (∑ k ∈ Finset.range (s + 1), bernsteinPolynomial ℝ (j + 1) k) y
  have h2 : eval y (-((j + 1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ j s) =
      -((j : ℝ) + 1) * (bernsteinPolynomial ℝ j s).eval y := by
    simp [eval_mul, eval_neg]
  rw [deriv_partial, h2] at h
  have e : (fun x => eval x (∑ k ∈ Finset.range (s + 1), bernsteinPolynomial ℝ (j + 1) k)) =
      Pfun j s := by
    funext x
    simp [Pfun, Polynomial.eval_finsetSum]
  rw [e] at h
  exact h

lemma Pfun_zero (j s : ℕ) : Pfun j s 0 = 1 := by
  simp [Pfun, bernsteinPolynomial.eval_at_0]

lemma bern_nonneg (n k : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval x := by
  simp only [bernsteinPolynomial, eval_mul, eval_pow, eval_natCast, eval_X, eval_sub, eval_one]
  have : 0 ≤ 1 - x := by linarith
  positivity

lemma pdf_eq (s m : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    betaPDF ((s : ℝ) + 1) ((m : ℝ) + 1) x =
      ENNReal.ofReal ((((s + m : ℕ) : ℝ) + 1) * (bernsteinPolynomial ℝ (s + m) s).eval x) := by
  rw [betaPDF_of_pos_lt_one hx0 hx1]
  congr 1
  have hb : beta ((s : ℝ) + 1) ((m : ℝ) + 1) =
      (s.factorial : ℝ) * m.factorial / ((s + m + 1).factorial : ℝ) := by
    unfold beta
    have : ((s : ℝ) + 1) + ((m : ℝ) + 1) = ((s + m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial]
  have hfac : ((s + m + 1).factorial : ℝ) =
      ((s + m : ℕ) + 1 : ℝ) * ((s + m).choose s : ℝ) * s.factorial * m.factorial := by
    have h1 := Nat.add_choose_mul_factorial_mul_factorial s m
    have hc : (s + m).choose s = (s + m).choose m := Nat.choose_symm_add
    rw [hc]
    have h2 : (s + m + 1).factorial = (s + m + 1) * (s + m).factorial := Nat.factorial_succ _
    rw [h2]
    push_cast
    rw [← h1]
    push_cast
    ring
  have hsf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hmf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  simp only [bernsteinPolynomial, eval_mul, eval_pow, eval_natCast, eval_X, eval_sub, eval_one]
  rw [hb, hfac, Nat.add_sub_cancel_left]
  have e1 : x ^ ((s : ℝ) + 1 - 1) = x ^ s := by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  have e2 : (1 - x) ^ ((m : ℝ) + 1 - 1) = (1 - x) ^ m := by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [e1, e2]
  field_simp


lemma cdf_val (s m : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    betaMeasure ((s : ℝ) + 1) ((m : ℝ) + 1) (Set.Iic y) =
      ENNReal.ofReal (1 - Pfun (s + m) s y) ∧ Pfun (s + m) s y ≤ 1 := by
  set j := s + m with hj
  set f : ℝ → ℝ := fun x => (((j : ℕ) : ℝ) + 1) * (bernsteinPolynomial ℝ j s).eval x with hf
  have hfc : Continuous f := by
    simp only [hf]; fun_prop
  have hfnn : ∀ x ∈ Set.Icc (0 : ℝ) y, 0 ≤ f x := by
    intro x hx
    simp only [hf]
    have := bern_nonneg j s x hx.1 (by linarith [hx.2])
    positivity
  have hint : ∫ x in (0 : ℝ)..y, f x = (1 - Pfun j s y) - (1 - Pfun j s 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => 1 - Pfun j s x) (fun x _ => ?_) (hfc.intervalIntegrable _ _)
    have := (hasDerivAt_Pfun j s x).const_sub 1
    convert this using 1
    simp only [hf]; ring
  rw [Pfun_zero] at hint
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..y, f x :=
    intervalIntegral.integral_nonneg hy0 (fun x hx => hfnn x hx)
  have hP : Pfun j s y ≤ 1 := by linarith
  refine ⟨?_, hP⟩
  rw [betaMeasure, withDensity_apply _ measurableSet_Iic, ← Set.Iic_union_Ioc_eq_Iic hy0,
    lintegral_union measurableSet_Ioc (Set.Iic_disjoint_Ioc le_rfl),
    setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x ≤ 0) => betaPDF_eq_zero_of_nonpos hx),
    zero_add,
    setLIntegral_congr_fun measurableSet_Ioc (fun x hx => pdf_eq s m x hx.1 (lt_of_le_of_lt hx.2 hy1))]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hy0, hint]; congr 1; ring
  · exact (hfc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx =>
      hfnn x ⟨hx.1.le, hx.2⟩)

lemma binomCDF_eq (j s : ℕ) (hs : s ≤ j) (y : ℝ) :
    AgrawalGoyalTS.TwoArmed.binomCDF (j + 1) y (s : ℝ) = Pfun j s y := by
  unfold AgrawalGoyalTS.TwoArmed.binomCDF Pfun
  have : (Finset.range (j + 1 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (s : ℝ)) =
      Finset.range (s + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_le]
    omega
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [AgrawalGoyalTS.TwoArmed.binomPMF, bernsteinPolynomial]


lemma lt_firstExceed_iff (y : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    ((n : ℕ∞) < AgrawalGoyalTS.TwoArmed.firstExceed y ω) ↔ ∀ i ≤ n, ω i ≤ y := by
  unfold AgrawalGoyalTS.TwoArmed.firstExceed
  constructor
  · intro h i hi
    by_contra hlt
    push_neg at hlt
    have h1 : (⨅ (n : ℕ) (_ : y < ω n), (n : ℕ∞)) ≤ i := iInf₂_le i hlt
    have h2 : (n : ℕ∞) < i := lt_of_lt_of_le h h1
    have : n < i := by exact_mod_cast h2
    omega
  · intro h
    have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ ⨅ (m : ℕ) (_ : y < ω m), (m : ℕ∞) := by
      refine le_iInf₂ fun m hm => ?_
      have : n < m := by
        by_contra hc
        push_neg at hc
        exact absurd (h m hc) (not_le.2 hm)
      exact_mod_cast this
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) h1

lemma toENNReal_tsum (X : ℕ∞) :
    (X : ENNReal) = ∑' n : ℕ, if (n : ℕ∞) < X then (1 : ENNReal) else 0 := by
  induction X using ENat.recTopCoe with
  | top =>
    simp [ENNReal.tsum_const_eq_top_of_ne_zero]
  | coe N =>
    rw [tsum_eq_sum (s := Finset.range N)]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ENNReal))
        (fun x hx => by simp [Nat.cast_lt, Finset.mem_range.1 hx])]
      simp
    · intro b hb
      have : ¬ (b : ℕ∞) < (N : ℕ∞) := by
        rw [Nat.cast_lt]; simpa using hb
      simp [this]

lemma expect_eq (y : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫⁻ ω, ENat.toENNReal (AgrawalGoyalTS.TwoArmed.firstExceed y ω) ∂(Measure.infinitePi (fun _ : ℕ => μ))
      = ∑' n : ℕ, (μ (Set.Iic y)) ^ (n + 1) := by
  set A : ℕ → Set (ℕ → ℝ) := fun n => Set.pi (↑(Finset.range (n + 1)) : Set ℕ) (fun _ => Set.Iic y)
    with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_Iic)
  have hmem : ∀ (n : ℕ) (ω : ℕ → ℝ), ((n : ℕ∞) < AgrawalGoyalTS.TwoArmed.firstExceed y ω) ↔ ω ∈ A n := by
    intro n ω
    rw [lt_firstExceed_iff]
    simp only [hA, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_Iic]
    constructor
    · intro h i hi; exact h i (by omega)
    · intro h i hi; exact h i (by omega)
  have h1 : ∀ ω, (ENat.toENNReal (AgrawalGoyalTS.TwoArmed.firstExceed y ω)) =
      ∑' n : ℕ, (A n).indicator (1 : (ℕ → ℝ) → ENNReal) ω := by
    intro ω
    rw [toENNReal_tsum]
    refine tsum_congr fun n => ?_
    by_cases h : ω ∈ A n
    · simp [h, (hmem n ω).2 h]
    · have : ¬ ((n : ℕ∞) < AgrawalGoyalTS.TwoArmed.firstExceed y ω) := fun h' => h ((hmem n ω).1 h')
      simp [h, this]
  simp_rw [h1]
  rw [lintegral_tsum (fun n => (measurable_one.indicator (hAm n)).aemeasurable)]
  refine tsum_congr fun n => ?_
  rw [lintegral_indicator_one (hAm n)]
  rw [hA]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => μ) (s := Finset.range (n + 1))
    (t := fun _ => Set.Iic y) (fun i _ => measurableSet_Iic)]
  simp

lemma geom_alg (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∑' n : ℕ, (ENNReal.ofReal (1 - c)) ^ (n + 1) = 1 / ENNReal.ofReal c - 1 := by
  have h1 : (1 : ENNReal) - ENNReal.ofReal (1 - c) = ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    congr 1; ring
  have h2 : ∑' n : ℕ, (ENNReal.ofReal (1 - c)) ^ (n + 1) =
      ENNReal.ofReal (1 - c) * (ENNReal.ofReal c)⁻¹ := by
    simp_rw [pow_succ']
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, h1]
  rw [h2, one_div, ← ENNReal.ofReal_inv_of_pos hc0, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
  congr 1
  field_simp

lemma Pfun_pos (j s : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) : 0 < Pfun j s y := by
  unfold Pfun
  have h := Finset.single_le_sum (f := fun k => (bernsteinPolynomial ℝ (j + 1) k).eval y)
    (fun k _ => bern_nonneg _ _ y hy0 hy1.le) (Finset.mem_range.2 (Nat.succ_pos s) : 0 ∈ Finset.range (s + 1))
  have h0 : (bernsteinPolynomial ℝ (j + 1) 0).eval y = (1 - y) ^ (j + 1) := by
    simp [bernsteinPolynomial]
  have : 0 < (1 - y) ^ (j + 1) := pow_pos (by linarith) _
  linarith

lemma Pfun_one (j s : ℕ) (hs : s ≤ j) : Pfun j s 1 = 0 := by
  unfold Pfun
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [bernsteinPolynomial.eval_at_1]
  have : k ≠ j + 1 := by have := Finset.mem_range.1 hk; omega
  simp [this]

end AGTAux

open AGTAux in
theorem solution (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    AgrawalGoyalTS.TwoArmed.betaCDF (α : ℝ) (β : ℝ) y =
      1 - AgrawalGoyalTS.TwoArmed.binomCDF (α + β - 1) y ((α : ℝ) - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, α = s + 1 := ⟨α - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, β = m + 1 := ⟨β - 1, by omega⟩
  have e1 : s + 1 + (m + 1) - 1 = (s + m) + 1 := by omega
  have e2 : (((s + 1 : ℕ) : ℝ) - 1) = (s : ℝ) := by push_cast; ring
  rw [e1, e2, binomCDF_eq _ _ (by omega)]
  unfold AgrawalGoyalTS.TwoArmed.betaCDF
  have e3 : (((s + 1 : ℕ) : ℝ)) = (s : ℝ) + 1 := by push_cast; ring
  have e4 : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  rw [e3, e4]
  rcases eq_or_lt_of_le hy1 with h1 | h1
  · subst h1
    rw [Pfun_one _ _ (by omega)]
    have hq : betaMeasure ((s : ℝ) + 1) ((m : ℝ) + 1) (Set.Iic 1) = 1 := by
      rw [← prob_compl_eq_zero_iff measurableSet_Iic, Set.compl_Iic, betaMeasure,
        withDensity_apply _ measurableSet_Ioi]
      exact setLIntegral_eq_zero measurableSet_Ioi (fun x (hx : 1 < x) => betaPDF_eq_zero_of_one_le hx.le)
    rw [hq]
    simp
  · obtain ⟨hq, hP⟩ := cdf_val s m y hy0 h1
    rw [hq, ENNReal.toReal_ofReal (by linarith)]
