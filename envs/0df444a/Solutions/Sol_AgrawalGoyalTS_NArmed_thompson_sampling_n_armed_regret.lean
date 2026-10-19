-- Prove2me | solution 1 for AgrawalGoyalTS.NArmed.thompson_sampling_n_armed_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T04:56:40.118465+00:00
-- url     : https://prove2.me/submissions/6b620057-16be-4c94-b56c-ab513a4bd97b

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace E20Hoeff

open AgrawalGoyalTS.TwoArmed

lemma hoeff_fin {n : ℕ} (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n)) (ℓ : Fin n → ℝ)
    (hℓ : ∀ i, -1 ≤ ℓ i ∧ ℓ i ≤ 1) (s : ℝ) :
    ∑ i, w i * Real.exp (s * ℓ i) ≤ Real.exp (s * ∑ i, w i * ℓ i + s ^ 2 / 2) := by
  classical
  obtain ⟨hw0, hw1⟩ := hw
  let μ : Measure (Fin n) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac i
  have hμs : ∀ j, μ {j} = ENNReal.ofReal (w j) := by
    intro j
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator]
  have hμr : ∀ j, μ.real {j} = w j := by
    intro j
    rw [measureReal_def, hμs, ENNReal.toReal_ofReal (hw0 j)]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]
  have hint : ∀ f : Fin n → ℝ, ∫ x, f x ∂μ = ∑ i, w i * f i := by
    intro f
    rw [integral_fintype (Integrable.of_finite)]
    simp [hμr]
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := -1) (b := 1)
    (Measurable.of_discrete).aemeasurable (Filter.Eventually.of_forall fun i => ⟨(hℓ i).1, (hℓ i).2⟩)
  have h2 := hH.mgf_le s
  have hc : ((‖(1:ℝ) - -1‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : ‖(1:ℝ) - -1‖₊ = 2 := by
      ext; simp; norm_num
    rw [this]; norm_num
  rw [hc] at h2
  simp only [mgf, hint, NNReal.coe_one, one_mul] at h2
  set m := ∑ i, w i * ℓ i
  have key : ∑ i, w i * Real.exp (s * ℓ i) =
      Real.exp (s * m) * ∑ i, w i * Real.exp (s * (ℓ i - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, Real.exp_sub]; field_simp
  rw [key, Real.exp_add]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- Hoeffding's lemma for a Bernoulli variable. -/
lemma bern_hoeff (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    p * Real.exp t + (1 - p) ≤ Real.exp (t * p + t ^ 2 / 8) := by
  have h := hoeff_fin (n := 2) ![1 - p, p] ⟨fun i => by fin_cases i <;> simp <;> linarith,
    by simp⟩ ![-1, 1] (fun i => by fin_cases i <;> norm_num) (t / 2)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e1 : p * Real.exp t + (1 - p) =
      Real.exp (t / 2) * ((1 - p) * Real.exp (t / 2 * -1) + p * Real.exp (t / 2 * 1)) := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (Real.exp (t / 2)) (1 - p), mul_assoc,
      ← Real.exp_add, mul_comm (Real.exp (t / 2)) p, mul_assoc, ← Real.exp_add]
    have : t / 2 + t / 2 * -1 = 0 := by ring
    have h2 : t / 2 + t / 2 * 1 = t := by ring
    rw [this, h2, Real.exp_zero]; ring
  rw [e1]
  calc Real.exp (t / 2) * ((1 - p) * Real.exp (t / 2 * -1) + p * Real.exp (t / 2 * 1))
      ≤ Real.exp (t / 2) * Real.exp (t / 2 * ((1 - p) * -1 + p * 1) + (t / 2) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (t * p + t ^ 2 / 8) := by rw [← Real.exp_add]; congr 1; ring

lemma pmf_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ binomPMF n p k := by
  unfold binomPMF
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma pmf_sum (n : ℕ) (p : ℝ) : ∑ k ∈ Finset.range (n + 1), binomPMF n p k = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold binomPMF; ring

lemma one_sub_cdf (n : ℕ) (p x : ℝ) :
    1 - binomCDF n p x =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) ≤ x), binomPMF n p k := by
  rw [← pmf_sum n p, binomCDF, ← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun k : ℕ => (k : ℝ) ≤ x)]
  ring

lemma mgf_sum (n : ℕ) (p r : ℝ) :
    ∑ k ∈ Finset.range (n + 1), binomPMF n p k * r ^ k = (p * r + (1 - p)) ^ n := by
  rw [add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold binomPMF; ring

lemma chernoff_upper (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x l : ℝ) (hl : 0 ≤ l) :
    1 - binomCDF n p x ≤ Real.exp (-l * x) * (p * Real.exp l + (1 - p)) ^ n := by
  rw [one_sub_cdf, ← mgf_sum, Finset.mul_sum]
  calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) ≤ x), binomPMF n p k
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) ≤ x),
          Real.exp (-l * x) * (binomPMF n p k * Real.exp l ^ k) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hkx : x < k := lt_of_not_ge (Finset.mem_filter.mp hk).2
        have h1 : 1 ≤ Real.exp (-l * x) * Real.exp l ^ k := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        have := pmf_nonneg n p hp0 hp1 k
        nlinarith
    _ ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (-l * x) * (binomPMF n p k * Real.exp l ^ k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k _ _
        have := pmf_nonneg n p hp0 hp1 k
        positivity

lemma chernoff_lower (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x l : ℝ) (hl : 0 ≤ l) :
    binomCDF n p x ≤ Real.exp (l * x) * (p * Real.exp (-l) + (1 - p)) ^ n := by
  rw [binomCDF, ← mgf_sum, Finset.mul_sum]
  calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x), binomPMF n p k
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
          Real.exp (l * x) * (binomPMF n p k * Real.exp (-l) ^ k) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hkx : (k : ℝ) ≤ x := (Finset.mem_filter.mp hk).2
        have h1 : 1 ≤ Real.exp (l * x) * Real.exp (-l) ^ k := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        have := pmf_nonneg n p hp0 hp1 k
        nlinarith
    _ ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (l * x) * (binomPMF n p k * Real.exp (-l) ^ k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k _ _
        have := pmf_nonneg n p hp0 hp1 k
        positivity

lemma pow_exp_le (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ Real.exp b) :
    a ^ n ≤ Real.exp (n * b) := by
  rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ ha h n

lemma upper_gen (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x l : ℝ) (hl : 0 ≤ l) :
    1 - binomCDF m p x ≤ Real.exp (-l * x + m * (l * p + l ^ 2 / 8)) := by
  refine (chernoff_upper m p hp0 hp1 x l hl).trans ?_
  rw [Real.exp_add]
  refine mul_le_mul_of_nonneg_left (pow_exp_le m (by
    have := Real.exp_pos l; nlinarith) (bern_hoeff p hp0 hp1 l)) (Real.exp_pos _).le

lemma lower_gen (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x l : ℝ) (hl : 0 ≤ l) :
    binomCDF m p x ≤ Real.exp (l * x + m * (-l * p + l ^ 2 / 8)) := by
  refine (chernoff_lower m p hp0 hp1 x l hl).trans ?_
  rw [Real.exp_add]
  refine mul_le_mul_of_nonneg_left (pow_exp_le m (by
    have := Real.exp_pos (-l); nlinarith) ?_) (Real.exp_pos _).le
  have := bern_hoeff p hp0 hp1 (-l)
  rw [neg_sq] at this
  convert this using 2

lemma cdf_eq_one (m : ℕ) (p x : ℝ) (hx : (m : ℝ) ≤ x) : binomCDF m p x = 1 := by
  rw [← pmf_sum m p, binomCDF, Finset.filter_true_of_mem]
  intro k hk
  have : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : (k : ℝ) ≤ m := by exact_mod_cast this
  linarith

end E20Hoeff

open E20Hoeff in
theorem binom_hoeff (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    AgrawalGoyalTS.TwoArmed.binomCDF n p ((n : ℝ) * p - (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - AgrawalGoyalTS.TwoArmed.binomCDF n p ((n : ℝ) * p + (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - AgrawalGoyalTS.TwoArmed.binomCDF (n + 1) p ((n : ℝ) * p + (n : ℝ) * δ) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (lower_gen n p hp0 hp1 _ (4 * δ) (by linarith)).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  · refine (upper_gen n p hp0 hp1 _ (4 * δ) (by linarith)).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  · rw [← Real.exp_sub]
    by_cases hbig : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * p + (n : ℝ) * δ
    · rw [cdf_eq_one _ _ _ hbig, sub_self]; exact (Real.exp_pos _).le
    · push Not at hbig
      push_cast at hbig
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine (upper_gen (n + 1) p hp0 hp1 _ (4 * δ * n / (n + 1)) (by positivity)).trans
        (Real.exp_le_exp.mpr ?_)
      push_cast
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have key : -(4 * δ * n / (n + 1)) * ((n : ℝ) * p + n * δ) +
          ((n : ℝ) + 1) * (4 * δ * n / (n + 1) * p + (4 * δ * n / (n + 1)) ^ 2 / 8) =
          (4 * δ * n * p - 2 * δ ^ 2 * n ^ 2) / (n + 1) := by
        field_simp; ring
      rw [key, div_le_iff₀ hn1]
      have hA : 0 ≤ 2 * ((n : ℝ) + 1 - n * p) - n * δ := by nlinarith
      have hB : 0 ≤ δ * (2 * ((n : ℝ) + 1 - n * p) - n * δ) := mul_nonneg hδ hA
      nlinarith

namespace E20Unif

open Polynomial

open AgrawalGoyalTS.TwoArmed

/-- Partial sums of the Bernstein basis of degree `m+1`. -/
noncomputable def bsum (m a : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (a + 1), bernsteinPolynomial ℝ (m + 1) k

lemma deriv_bsum (m a : ℕ) :
    derivative (bsum m a) = -((m : ℝ[X]) + 1) * bernsteinPolynomial ℝ m a := by
  induction a with
  | zero =>
    simp only [bsum, zero_add, Finset.range_one, Finset.sum_singleton]
    rw [bernsteinPolynomial.derivative_zero]
    push_cast
    simp
  | succ a ih =>
    rw [bsum, Finset.sum_range_succ, derivative_add, ← bsum, ih,
      bernsteinPolynomial.derivative_succ_aux]
    ring

lemma eval_bern (n k : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ n k).eval x = (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
  simp [bernsteinPolynomial, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_natCast]

lemma bsum_eval0 (m a : ℕ) : (bsum m a).eval 0 = 1 := by
  simp only [bsum, eval_finsetSum, bernsteinPolynomial.eval_at_0]
  rw [Finset.sum_ite_eq' (Finset.range (a + 1)) 0 (fun _ => (1 : ℝ))]
  simp

lemma bsum_eval1 (m a : ℕ) (ha : a ≤ m) : (bsum m a).eval 1 = 0 := by
  simp only [bsum, eval_finsetSum, bernsteinPolynomial.eval_at_1]
  apply Finset.sum_eq_zero
  intro k hk
  have : k ≠ m + 1 := by
    have := Finset.mem_range.mp hk; omega
  simp [this]

lemma ftc (m a : ℕ) (y : ℝ) :
    ((m : ℝ) + 1) * ∫ x in (0:ℝ)..y, (bernsteinPolynomial ℝ m a).eval x =
      1 - (bsum m a).eval y := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => (bsum m a).eval x) (f' := fun x => (derivative (bsum m a)).eval x)
    (a := 0) (b := y) (fun x _ => Polynomial.hasDerivAt _ x)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  rw [deriv_bsum] at h
  simp only [eval_mul, eval_neg, eval_add, eval_natCast, eval_one] at h
  rw [intervalIntegral.integral_const_mul, bsum_eval0] at h
  linarith

lemma binomCDF_eq_bsum (m a : ℕ) (ha : a ≤ m + 1) (y : ℝ) :
    binomCDF (m + 1) y (a : ℝ) = (bsum m a).eval y := by
  unfold binomCDF bsum
  rw [eval_finsetSum]
  have : (Finset.range (m + 1 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (a : ℝ)) = Finset.range (a + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_le]; omega
  rw [this]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [eval_bern]; rfl

lemma pmf_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ binomPMF n p k := by
  unfold binomPMF
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma pmf_sum (n : ℕ) (p : ℝ) : ∑ k ∈ Finset.range (n + 1), binomPMF n p k = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold binomPMF; ring

lemma pmf_eq_bern (n k : ℕ) (x : ℝ) : binomPMF n x k = (bernsteinPolynomial ℝ n k).eval x := by
  rw [eval_bern]; rfl

/-- `(m+1) ∫_y^1 B_{m,a} = F_{m+1,y}(a)`. -/
lemma int_tail (m a : ℕ) (ha : a ≤ m) (y : ℝ) :
    ((m : ℝ) + 1) * ∫ x in y..1, (bernsteinPolynomial ℝ m a).eval x = (bsum m a).eval y := by
  have h1 := ftc m a 1
  have h2 := ftc m a y
  rw [bsum_eval1 m a ha] at h1
  have hi : IntervalIntegrable (fun x => (bernsteinPolynomial ℝ m a).eval x) volume 0 y :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => (bernsteinPolynomial ℝ m a).eval x) volume y 1 :=
    (Polynomial.continuous _).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hi2, mul_add] at h1
  linarith

/-- `θ ↦ F_{m+1,θ}(a)` is antitone on `[0,1]`. -/
lemma bsum_anti (m a : ℕ) {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h1 : θ₂ ≤ 1) :
    (bsum m a).eval θ₂ ≤ (bsum m a).eval θ₁ := by
  have e1 := ftc m a θ₁
  have e2 := ftc m a θ₂
  have hi : IntervalIntegrable (fun x => (bernsteinPolynomial ℝ m a).eval x) volume 0 θ₁ :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => (bernsteinPolynomial ℝ m a).eval x) volume θ₁ θ₂ :=
    (Polynomial.continuous _).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hi2, mul_add] at e2
  have hnn : 0 ≤ ∫ x in θ₁..θ₂, (bernsteinPolynomial ℝ m a).eval x := by
    refine intervalIntegral.integral_nonneg h12 (fun x hx => ?_)
    rw [eval_bern]
    have : 0 ≤ 1 - x := by linarith [hx.2]
    have : 0 ≤ x := le_trans h0 hx.1
    positivity
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg hm hnn]

/-- Abel summation. -/
lemma abel (f g : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range (n + 1), f s * g s =
      g n * ∑ s ∈ Finset.range (n + 1), f s +
        ∑ j ∈ Finset.range n, (g j - g (j + 1)) * ∑ s ∈ Finset.range (j + 1), f s := by
  induction n with
  | zero => simp [mul_comm]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun s => f s * g s), ih,
      Finset.sum_range_succ (fun j => (g j - g (j + 1)) * ∑ s ∈ Finset.range (j + 1), f s),
      Finset.sum_range_succ f (n + 1)]
    ring

/-- Binomial expectation of an antitone function is antitone in the success probability. -/
lemma binom_exp_anti (k : ℕ) (g : ℕ → ℝ) (hg : ∀ j, g (j + 1) ≤ g j)
    {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h1 : θ₂ ≤ 1) :
    ∑ s ∈ Finset.range (k + 1), binomPMF k θ₂ s * g s ≤
      ∑ s ∈ Finset.range (k + 1), binomPMF k θ₁ s * g s := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [binomPMF]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [abel (fun s => binomPMF (m + 1) θ₂ s) g, abel (fun s => binomPMF (m + 1) θ₁ s) g,
    pmf_sum, pmf_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ ?_)
  rotate_left
  · linarith [hg j]
  · have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e : ∀ θ : ℝ, ∑ s ∈ Finset.range (j + 1), binomPMF (m + 1) θ s = (bsum m j).eval θ := by
      intro θ
      unfold bsum
      rw [eval_finsetSum]
      exact Finset.sum_congr rfl (fun s _ => pmf_eq_bern _ _ _)
    rw [e, e]
    exact bsum_anti m j h0 h12 h1

lemma cdf_pos (n : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) (s : ℕ) :
    0 < binomCDF n y s := by
  unfold binomCDF
  have hmem : (0 : ℕ) ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (s : ℝ)) := by
    simp
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => pmf_nonneg n y hy0 hy1.le k) hmem)
  unfold binomPMF
  have : 0 < 1 - y := by linarith
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  positivity

lemma cdf_mono (n : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (s : ℕ) :
    binomCDF n y s ≤ binomCDF n y (s + 1 : ℕ) := by
  unfold binomCDF
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => pmf_nonneg n y hy0 hy1 k)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  refine ⟨hk.1, ?_⟩
  push_cast
  linarith [hk.2]

/-- UNIFORM BOUND: `E_{s ∼ Bin(k,μ)} [1 / F_{k+1,y}(s)] ≤ 1/(μ - y)` for every `k`. -/
theorem unif (k : ℕ) (μ y : ℝ) (hy0 : 0 ≤ y) (hyμ : y < μ) (hμ1 : μ ≤ 1) :
    ∑ s ∈ Finset.range (k + 1), binomPMF k μ s / binomCDF (k + 1) y s ≤ 1 / (μ - y) := by
  have hy1 : y < 1 := lt_of_lt_of_le hyμ hμ1
  set g : ℕ → ℝ := fun s => 1 / binomCDF (k + 1) y s with hgdef
  have hqpos : ∀ s : ℕ, 0 < binomCDF (k + 1) y s := cdf_pos (k + 1) y hy0 hy1
  have hg : ∀ j, g (j + 1) ≤ g j := by
    intro j
    simp only [hgdef]
    exact one_div_le_one_div_of_le (hqpos j) (by exact_mod_cast cdf_mono (k + 1) y hy0 hy1.le j)
  have hg0 : ∀ j, 0 ≤ g j := fun j => (one_div_pos.mpr (hqpos j)).le
  set E : ℝ → ℝ := fun θ => ∑ s ∈ Finset.range (k + 1), binomPMF k θ s * g s with hE
  have hEc : Continuous E := by
    simp only [hE, binomPMF]
    exact continuous_finsetSum _ (fun s _ => by fun_prop)
  have hEnn : ∀ θ, 0 ≤ θ → θ ≤ 1 → 0 ≤ E θ := fun θ h0 h1 =>
    Finset.sum_nonneg (fun s _ => mul_nonneg (pmf_nonneg k θ h0 h1 s) (hg0 s))
  have hlhs : ∑ s ∈ Finset.range (k + 1), binomPMF k μ s / binomCDF (k + 1) y s = E μ := by
    simp only [hE, hgdef]
    refine Finset.sum_congr rfl (fun s _ => by ring)
  -- the integral over [y,1]
  have hint : ∫ θ in y..1, E θ = 1 := by
    simp only [hE]
    rw [intervalIntegral.integral_finsetSum (fun s _ =>
      ((by simp only [binomPMF]; fun_prop : Continuous (fun θ : ℝ => binomPMF k θ s * g s))).intervalIntegrable _ _)]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have : ∀ s ∈ Finset.range (k + 1), ∫ θ in y..1, binomPMF k θ s * g s = 1 / ((k : ℝ) + 1) := by
      intro s hs
      have hsk : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [intervalIntegral.integral_mul_const]
      simp_rw [pmf_eq_bern]
      have ht := int_tail k s hsk y
      rw [← binomCDF_eq_bsum k s (by omega) y] at ht
      have hq := hqpos s
      simp only [hgdef]
      field_simp
      linarith
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  have hmono : (μ - y) * E μ ≤ ∫ θ in y..μ, E θ := by
    have := intervalIntegral.integral_mono_on hyμ.le ((continuous_const (y := E μ)).intervalIntegrable (μ := volume) y μ)
      (hEc.intervalIntegrable y μ) (fun θ hθ =>
        binom_exp_anti k g hg (le_trans hy0 hθ.1) hθ.2 hμ1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hsplit : ∫ θ in y..μ, E θ ≤ ∫ θ in y..1, E θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hEc.intervalIntegrable y μ)
      (hEc.intervalIntegrable μ 1)]
    have : 0 ≤ ∫ θ in μ..1, E θ :=
      intervalIntegral.integral_nonneg hμ1 (fun θ hθ =>
        hEnn θ (le_trans (le_trans hy0 hyμ.le) hθ.1) hθ.2)
    linarith
  rw [hlhs, le_div_iff₀ (by linarith)]
  linarith [hmono, hsplit, hint]

end E20Unif


namespace E20CSum

open AgrawalGoyalTS.TwoArmed

lemma cdf_mono_x (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {x x' : ℝ} (h : x ≤ x') :
    binomCDF n p x ≤ binomCDF n p x' := by
  unfold binomCDF
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => E20Unif.pmf_nonneg n p hp0 hp1 k)
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.trans h⟩

lemma exp_neg_two_log (T : ℝ) (hT : 0 < T) : Real.exp (-2 * Real.log T) = 1 / T ^ 2 := by
  have : -2 * Real.log T = -(Real.log (T ^ 2)) := by rw [Real.log_pow]; push_cast; ring
  rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- Per-`k` bound in the large-`k` regime. -/
lemma large_k (T : ℕ) (hT : 2 ≤ T) (μ y d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hy0 : 0 ≤ y)
    (hyμ : μ - y = d) (hμ1 : μ ≤ 1) (k : ℕ) (hk : (4 * Real.log T + 4) / d ^ 2 ≤ k) :
    ∑ s ∈ Finset.range (k + 1),
      min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s ≤ 2 / T := by
  have hμ0 : 0 ≤ μ := by linarith
  have hy1 : y < 1 := by linarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hkd : 4 * Real.log T + 4 ≤ k * d ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- the exponential is at most e^{-2} / T^2
  have hexp : Real.exp (-2 * (k : ℝ) * (d / 2) ^ 2) ≤ 1 / T ^ 2 := by
    rw [← exp_neg_two_log T hTpos]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp2 : Real.exp (4 * (d / 2)) / Real.exp (2 * (k : ℝ) * (d / 2) ^ 2) ≤ 1 / T ^ 2 := by
    rw [← Real.exp_sub, ← exp_neg_two_log T hTpos]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hHo := binom_hoeff k μ hμ0 hμ1 (d / 2) (by linarith)
  have hHo' := binom_hoeff k y hy0 hy1.le (d / 2) (by linarith)
  set z : ℝ := (k : ℝ) * μ - (k : ℝ) * (d / 2) with hz
  have hz' : (k : ℝ) * y + (k : ℝ) * (d / 2) = z := by rw [hz]; nlinarith [hyμ]
  rw [hz'] at hHo'
  -- split the sum at z
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (k + 1)) (fun s : ℕ => (s : ℝ) ≤ z)]
  have hq : ∀ s : ℕ, 0 < binomCDF (k + 1) y s := E20Unif.cdf_pos (k + 1) y hy0 hy1
  have h1 : ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => (s : ℝ) ≤ z),
      min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s ≤ 1 / T := by
    calc _ ≤ ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => (s : ℝ) ≤ z), (T : ℝ) * binomPMF k μ s :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (min_le_right _ _)
            (E20Unif.pmf_nonneg k μ hμ0 hμ1 s))
      _ = T * binomCDF k μ z := by rw [← Finset.mul_sum]; rfl
      _ ≤ T * (1 / T ^ 2) := by
          gcongr
          exact hHo.1.trans hexp
      _ = 1 / T := by field_simp
  have h2 : ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => ¬ (s : ℝ) ≤ z),
      min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s ≤
        2 / T ^ 2 := by
    have hpt : ∀ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => ¬ (s : ℝ) ≤ z),
        min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) ≤ 2 / T ^ 2 := by
      intro s hs
      have hsz : z ≤ (s : ℝ) := le_of_lt (not_le.mp (Finset.mem_filter.mp hs).2)
      have hε : 1 - binomCDF (k + 1) y s ≤ 1 / T ^ 2 :=
        (sub_le_sub_left (cdf_mono_x (k + 1) y hy0 hy1.le hsz) 1).trans (hHo'.2.2.trans hexp2)
      have hT4 : (1 : ℝ) / (T : ℝ) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have hqs := hq s
      have hq2 : 1 / 2 ≤ binomCDF (k + 1) y s := by linarith
      refine (min_le_left _ _).trans ?_
      rw [div_le_iff₀ hqs]
      have hnn : (0 : ℝ) ≤ 1 / (T : ℝ) ^ 2 := by positivity
      have h2q : 1 ≤ 2 * binomCDF (k + 1) y s := by linarith
      calc 1 - binomCDF (k + 1) y s ≤ 1 / (T : ℝ) ^ 2 := hε
        _ = 1 / (T : ℝ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ 1 / (T : ℝ) ^ 2 * (2 * binomCDF (k + 1) y s) := mul_le_mul_of_nonneg_left h2q hnn
        _ = 2 / (T : ℝ) ^ 2 * binomCDF (k + 1) y s := by ring
    calc _ ≤ ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => ¬ (s : ℝ) ≤ z),
          2 / T ^ 2 * binomPMF k μ s :=
          Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_right (hpt s hs)
            (E20Unif.pmf_nonneg k μ hμ0 hμ1 s))
      _ = 2 / T ^ 2 * ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => ¬ (s : ℝ) ≤ z),
          binomPMF k μ s := by rw [Finset.mul_sum]
      _ ≤ 2 / T ^ 2 * 1 := by
          gcongr
          rw [← E20Unif.pmf_sum k μ]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun s _ _ => E20Unif.pmf_nonneg k μ hμ0 hμ1 s)
      _ = 2 / T ^ 2 := mul_one _
  have h3 : (2 : ℝ) / (T : ℝ) ^ 2 ≤ 1 / (T : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hTpos]; nlinarith
  calc _ ≤ (1 : ℝ) / (T : ℝ) + 1 / (T : ℝ) := add_le_add h1 (h2.trans h3)
    _ = 2 / T := by ring

/-- Per-`k` bound in the small-`k` regime (the uniform bound). -/
lemma small_k (T : ℕ) (μ y d : ℝ) (hd : 0 < d) (hy0 : 0 ≤ y)
    (hyμ : μ - y = d) (hμ1 : μ ≤ 1) (k : ℕ) :
    ∑ s ∈ Finset.range (k + 1),
      min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s ≤ 1 / d := by
  have hμ0 : 0 ≤ μ := by linarith
  have hy1 : y < 1 := by linarith
  have hu := E20Unif.unif k μ y hy0 (by linarith) hμ1
  rw [hyμ] at hu
  refine le_trans (Finset.sum_le_sum (fun s _ => ?_)) hu
  have hq := E20Unif.cdf_pos (k + 1) y hy0 hy1 s
  have hf := E20Unif.pmf_nonneg k μ hμ0 hμ1 s
  have hq1 : binomCDF (k + 1) y s ≤ 1 := by
    rw [← E20Unif.pmf_sum (k + 1) y]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => E20Unif.pmf_nonneg (k + 1) y hy0 hy1.le s)
  calc min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s
      ≤ ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) * binomPMF k μ s :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hf
    _ ≤ (1 / binomCDF (k + 1) y s) * binomPMF k μ s := by
        gcongr; linarith
    _ = binomPMF k μ s / binomCDF (k + 1) y s := by ring

/-- (C) analytic sum. -/
theorem csum (T : ℕ) (hT : 2 ≤ T) (μ y d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hy0 : 0 ≤ y)
    (hyμ : μ - y = d) (hμ1 : μ ≤ 1) :
    ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
      min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ s ≤
        ((4 * Real.log T + 4) / d ^ 2 + 1) / d + 2 := by
  set L : ℝ := (4 * Real.log T + 4) / d ^ 2 with hL
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun k : ℕ => (k : ℝ) < L)]
  refine add_le_add ?_ ?_
  · calc _ ≤ ∑ k ∈ (Finset.range T).filter (fun k : ℕ => (k : ℝ) < L), 1 / d :=
          Finset.sum_le_sum (fun k _ => small_k T μ y d hd hy0 hyμ hμ1 k)
      _ = ((Finset.range T).filter (fun k : ℕ => (k : ℝ) < L)).card * (1 / d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L + 1) * (1 / d) := by
          gcongr
          have hsub : (Finset.range T).filter (fun k : ℕ => (k : ℝ) < L) ⊆ Finset.range (⌈L⌉₊) := by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
            exact Nat.lt_ceil.mpr hk.2
          calc (((Finset.range T).filter (fun k : ℕ => (k : ℝ) < L)).card : ℝ)
              ≤ (Finset.range (⌈L⌉₊)).card := by exact_mod_cast Finset.card_le_card hsub
            _ = (⌈L⌉₊ : ℝ) := by rw [Finset.card_range]
            _ ≤ L + 1 := by
                have hL0 : 0 ≤ L := by
                  have : 0 ≤ Real.log T := Real.log_nonneg (by
                    have : (2 : ℝ) ≤ T := by exact_mod_cast hT
                    linarith)
                  positivity
                exact (Nat.ceil_lt_add_one hL0).le
      _ = (L + 1) / d := by ring
  · calc _ ≤ ∑ k ∈ (Finset.range T).filter (fun k : ℕ => ¬ (k : ℝ) < L), 2 / (T : ℝ) :=
          Finset.sum_le_sum (fun k hk => large_k T hT μ y d hd hd1 hy0 hyμ hμ1 k
            (not_lt.mp (Finset.mem_filter.mp hk).2))
      _ = ((Finset.range T).filter (fun k : ℕ => ¬ (k : ℝ) < L)).card * (2 / T) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T : ℝ) * (2 / T) := by
          gcongr
          have := Finset.card_filter_le (Finset.range T) (fun k : ℕ => ¬ (k : ℝ) < L)
          rw [Finset.card_range] at this
          exact_mod_cast this
      _ = 2 := by field_simp

end E20CSum

namespace E20Fact1

open Polynomial

/-- Partial sums of the Bernstein basis of degree `m+1`. -/
noncomputable def bsum (m a : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (a + 1), bernsteinPolynomial ℝ (m + 1) k

lemma deriv_bsum (m a : ℕ) :
    derivative (bsum m a) = -((m : ℝ[X]) + 1) * bernsteinPolynomial ℝ m a := by
  induction a with
  | zero =>
    simp only [bsum, zero_add, Finset.range_one, Finset.sum_singleton]
    rw [bernsteinPolynomial.derivative_zero]
    push_cast
    simp
  | succ a ih =>
    rw [bsum, Finset.sum_range_succ, derivative_add, ← bsum, ih,
      bernsteinPolynomial.derivative_succ_aux]
    ring

lemma eval_bern (n k : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ n k).eval x = (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
  simp [bernsteinPolynomial, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_natCast]

lemma bsum_eval0 (m a : ℕ) : (bsum m a).eval 0 = 1 := by
  simp only [bsum, eval_finsetSum, bernsteinPolynomial.eval_at_0]
  rw [Finset.sum_ite_eq' (Finset.range (a + 1)) 0 (fun _ => (1 : ℝ))]
  simp

lemma bsum_eval1 (m a : ℕ) (ha : a ≤ m) : (bsum m a).eval 1 = 0 := by
  simp only [bsum, eval_finsetSum, bernsteinPolynomial.eval_at_1]
  apply Finset.sum_eq_zero
  intro k hk
  have : k ≠ m + 1 := by
    have := Finset.mem_range.mp hk; omega
  simp [this]

/-- FTC: `(m+1) ∫_0^y B_{m,a} = 1 - bsum m a (y)`. -/
lemma ftc (m a : ℕ) (y : ℝ) :
    ((m : ℝ) + 1) * ∫ x in (0:ℝ)..y, (bernsteinPolynomial ℝ m a).eval x =
      1 - (bsum m a).eval y := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => (bsum m a).eval x) (f' := fun x => (derivative (bsum m a)).eval x)
    (a := 0) (b := y) (fun x _ => Polynomial.hasDerivAt _ x)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  rw [deriv_bsum] at h
  simp only [eval_mul, eval_neg, eval_add, eval_natCast, eval_one] at h
  rw [intervalIntegral.integral_const_mul, bsum_eval0] at h
  linarith

/-- The real density part. -/
noncomputable def g (a b : ℕ) (x : ℝ) : ℝ :=
  (1 / beta ((a : ℝ) + 1) ((b : ℝ) + 1)) * x ^ a * (1 - x) ^ b

lemma g_cont (a b : ℕ) : Continuous (g a b) := by
  unfold g; fun_prop

lemma betaPDF_eq_ind (a b : ℕ) (x : ℝ) :
    betaPDF ((a : ℝ) + 1) ((b : ℝ) + 1) x =
      (Set.Ioo (0:ℝ) 1).indicator (fun x => ENNReal.ofReal (g a b x)) x := by
  by_cases hx : x ∈ Set.Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem hx, betaPDF_of_pos_lt_one hx.1 hx.2, g]
    congr 1
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  · rw [Set.indicator_of_notMem hx, betaPDF_eq, if_neg (by simpa using hx)]
    simp

lemma g_nonneg (a b : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ g a b x := by
  unfold g
  have := beta_pos (α := (a : ℝ) + 1) (β := (b : ℝ) + 1) (by positivity) (by positivity)
  have : 0 ≤ 1 - x := by linarith
  positivity

lemma measure_Iic (a b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Iic y) =
      ENNReal.ofReal (∫ x in (0:ℝ)..y, g a b x) := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Iic]
  simp_rw [betaPDF_eq_ind]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    intervalIntegral.integral_of_le hy0]
  have key : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Icc 0 1 →
      ∫⁻ x in S, ENNReal.ofReal (g a b x) = ENNReal.ofReal (∫ x in S, g a b x) := by
    intro S hS hsub
    rw [ofReal_integral_eq_lintegral_ofReal]
    · exact ((g_cont a b).integrableOn_Icc).mono_set hsub
    · exact (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall
        (fun x hx => g_nonneg a b (hsub hx).1 (hsub hx).2))
  rcases hy1.lt_or_eq with hlt | heq
  · have hset : Set.Ioo (0:ℝ) 1 ∩ Set.Iic y = Set.Ioc 0 y := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [hset, key _ measurableSet_Ioc (fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)]
  · subst heq
    have hset : Set.Ioo (0:ℝ) 1 ∩ Set.Iic 1 = Set.Ioo 0 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic]
      constructor
      · rintro ⟨h, _⟩; exact h
      · intro h; exact ⟨h, h.2.le⟩
    rw [hset, key _ measurableSet_Ioo (fun x hx => ⟨hx.1.le, hx.2.le⟩),
      integral_Ioc_eq_integral_Ioo]

lemma g_eq (a b : ℕ) (x : ℝ) :
    g a b x = (1 / beta ((a : ℝ) + 1) ((b : ℝ) + 1)) / ((a + b).choose a : ℝ) *
      (bernsteinPolynomial ℝ (a + b) a).eval x := by
  rw [eval_bern, g, Nat.add_sub_cancel_left]
  have : ((a + b).choose a : ℝ) ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_right a b); positivity
  field_simp

lemma inv_beta (a b : ℕ) :
    1 / beta ((a : ℝ) + 1) ((b : ℝ) + 1) = (((a + b : ℕ) : ℝ) + 1) * ((a + b).choose a : ℝ) := by
  have hB := beta_pos (α := (a : ℝ) + 1) (β := (b : ℝ) + 1) (by positivity) (by positivity)
  have hc : ((a + b).choose a : ℝ) ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_right a b); positivity
  have := isProbabilityMeasureBeta (α := (a : ℝ) + 1) (β := (b : ℝ) + 1)
    (by positivity) (by positivity)
  have h1 : betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Iic 1) = 1 := by
    refine (prob_compl_eq_zero_iff measurableSet_Iic).mp ?_
    rw [Set.compl_Iic, betaMeasure, withDensity_apply _ measurableSet_Ioi]
    exact setLIntegral_eq_zero measurableSet_Ioi
      (fun x (hx : 1 < x) => betaPDF_eq_zero_of_one_le hx.le)
  rw [measure_Iic a b 1 zero_le_one le_rfl] at h1
  have hI : ∫ x in (0:ℝ)..1, g a b x = 1 := by
    have hnn : 0 ≤ ∫ x in (0:ℝ)..1, g a b x :=
      intervalIntegral.integral_nonneg zero_le_one (fun x hx => g_nonneg a b hx.1 hx.2)
    have := congrArg ENNReal.toReal h1
    rwa [ENNReal.toReal_ofReal hnn, ENNReal.toReal_one] at this
  have hF := ftc (a + b) a 1
  rw [bsum_eval1 _ _ (Nat.le_add_right a b), sub_zero] at hF
  simp_rw [g_eq] at hI
  rw [intervalIntegral.integral_const_mul] at hI
  set J := ∫ x in (0:ℝ)..1, (bernsteinPolynomial ℝ (a + b) a).eval x
  set c := 1 / beta ((a : ℝ) + 1) ((b : ℝ) + 1)
  push_cast at hF ⊢
  have hJ : J ≠ 0 := by intro h; rw [h, mul_zero] at hF; exact zero_ne_one hF
  field_simp at hI
  have : c = ((a : ℝ) + b + 1) * ((a + b).choose a : ℝ) := by
    have e1 : c * J = ((a + b).choose a : ℝ) := by linarith
    have e2 : ((a : ℝ) + b + 1) * J = 1 := hF
    have : c * J = ((a : ℝ) + b + 1) * ((a + b).choose a : ℝ) * J := by
      rw [e1, mul_comm _ J, ← mul_assoc, mul_comm J, e2, one_mul]
    exact mul_right_cancel₀ hJ this
  rw [this]

/-- Fact 1 in `bsum` form. -/
lemma beta_cdf_bsum (a b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    AgrawalGoyalTS.TwoArmed.betaCDF ((a : ℝ) + 1) ((b : ℝ) + 1) y = 1 - (bsum (a + b) a).eval y := by
  unfold AgrawalGoyalTS.TwoArmed.betaCDF
  rw [measure_Iic a b y hy0 hy1, ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hy0 (fun x hx => g_nonneg a b hx.1 (hx.2.trans hy1)))]
  simp_rw [g_eq]
  rw [intervalIntegral.integral_const_mul, ← ftc (a + b) a y, inv_beta]
  have hc : ((a + b).choose a : ℝ) ≠ 0 := by
    have := Nat.choose_pos (Nat.le_add_right a b); positivity
  field_simp

lemma binomCDF_eq_bsum (m a : ℕ) (ha : a ≤ m + 1) (y : ℝ) :
    AgrawalGoyalTS.TwoArmed.binomCDF (m + 1) y (a : ℝ) = (bsum m a).eval y := by
  unfold AgrawalGoyalTS.TwoArmed.binomCDF bsum
  rw [eval_finsetSum]
  have : (Finset.range (m + 1 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (a : ℝ)) = Finset.range (a + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_le]; omega
  rw [this]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [eval_bern]; rfl

end E20Fact1

open E20Fact1 in
theorem fact1 (α β : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    AgrawalGoyalTS.TwoArmed.betaCDF (α : ℝ) (β : ℝ) y =
      1 - AgrawalGoyalTS.TwoArmed.binomCDF (α + β - 1) y ((α : ℝ) - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  have e : a + 1 + (b + 1) - 1 = (a + b) + 1 := by omega
  rw [e]
  push_cast
  rw [add_sub_cancel_right, binomCDF_eq_bsum (a + b) a (by omega), beta_cdf_bsum a b y hy0 hy1]

open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed AgrawalGoyalTS.NArmed

namespace E20FW

variable {N : ℕ} [NeZero N]

lemma tsCounts_succ' (ω : TSOmega N) (t : ℕ) :
    tsCounts ω (t + 1) =
      if ((ω.2.2 (tsArm ω t, t) : ℝ) < ω.2.1 (tsArm ω t, t)) then
        (Function.update (tsCounts ω t).1 (tsArm ω t) ((tsCounts ω t).1 (tsArm ω t) + 1),
          (tsCounts ω t).2)
      else ((tsCounts ω t).1,
        Function.update (tsCounts ω t).2 (tsArm ω t) ((tsCounts ω t).2 (tsArm ω t) + 1)) := by
  rfl

lemma tsPlays_succ (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    tsPlays ω (t + 1) i = tsPlays ω t i + if tsArm ω t = i then 1 else 0 := by
  unfold tsPlays
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma tsPlays_eq (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    tsPlays ω t i = (tsCounts ω t).1 i + (tsCounts ω t).2 i := by
  induction t with
  | zero => simp [tsPlays, tsCounts]
  | succ t ih =>
    rw [tsPlays_succ, ih, tsCounts_succ']
    by_cases ha : tsArm ω t = i
    · subst ha
      split_ifs <;> simp <;> omega
    · have hb : i ≠ tsArm ω t := Ne.symm ha
      split_ifs <;> simp [Function.update_of_ne hb, ha]


lemma mset_factor {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] {κ : Ω → β} (hκ : Measurable κ) (P : Ω → Prop)
    (hP : ∀ ω ω', κ ω = κ ω' → P ω → P ω') : MeasurableSet {ω | P ω} := by
  have : {ω | P ω} = κ ⁻¹' (κ '' {ω | P ω}) := by
    ext ω
    constructor
    · intro h
      exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', h', e⟩
      exact hP _ _ e h'
  rw [this]
  exact hκ (Set.to_countable _).measurableSet

lemma argmaxMin_measurable : Measurable (argmaxMin : (Fin N → ℝ) → Fin N) := by
  let d : (Fin N → ℝ) → (Fin N → Bool) := fun θ k => decide (∀ j, θ j ≤ θ k)
  have hd : Measurable d := by
    refine measurable_pi_lambda _ (fun k => measurable_to_bool ?_)
    have : (fun θ : Fin N → ℝ => d θ k) ⁻¹' {true} = ⋂ j, {θ | θ j ≤ θ k} := by
      ext θ
      simp [d]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j) (measurable_pi_apply k)
  refine measurable_to_countable' fun i => mset_factor hd (fun θ => argmaxMin θ = i) ?_
  intro θ θ' h hθ
  have hθ' : argmaxMin θ = i := hθ
  show argmaxMin θ' = i
  have hS : (Finset.univ.filter (fun i => ∀ j, θ j ≤ θ i)) =
      Finset.univ.filter (fun i => ∀ j, θ' j ≤ θ' i) := by
    ext k
    have := congrFun h k
    simp only [d, decide_eq_decide] at this
    simp [this]
  rw [← hθ']
  unfold argmaxMin
  rw [hS]

lemma tsCounts_measurable (t : ℕ) : Measurable (fun ω : TSOmega N => tsCounts ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let F : TSOmega N × ((Fin N → ℕ) × (Fin N → ℕ)) → (Fin N → ℕ) × (Fin N → ℕ) := fun p =>
      if ((p.1.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)), t) : ℝ) <
          p.1.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)), t)) then
        (Function.update p.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)))
          (p.2.1 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i))) + 1), p.2.2)
      else (p.2.1, Function.update p.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i)))
          (p.2.2 (argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i))) + 1))
    have hF : Measurable F := by
      apply measurable_from_prod_countable_left
      intro c
      let G : TSOmega N × Fin N → (Fin N → ℕ) × (Fin N → ℕ) := fun q =>
        if ((q.1.2.2 (q.2, t) : ℝ) < q.1.2.1 (q.2, t)) then
          (Function.update c.1 q.2 (c.1 q.2 + 1), c.2)
        else (c.1, Function.update c.2 q.2 (c.2 q.2 + 1))
      have hG : Measurable G := by
        apply measurable_from_prod_countable_left
        intro a
        show Measurable fun x : TSOmega N =>
          if ((x.2.2 (a, t) : ℝ) < x.2.1 (a, t)) then (Function.update c.1 a (c.1 a + 1), c.2)
          else (c.1, Function.update c.2 a (c.2 a + 1))
        refine Measurable.ite ?_ measurable_const measurable_const
        exact measurableSet_lt
          (measurable_subtype_coe.comp ((measurable_pi_apply (a, t)).comp
            (measurable_snd.comp measurable_snd)))
          ((measurable_pi_apply (a, t)).comp (measurable_fst.comp measurable_snd))
      have hA : Measurable (fun ω : TSOmega N => argmaxMin (fun i => ω.1 (i, t, c.1 i, c.2 i))) :=
        argmaxMin_measurable.comp
          (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst)
      exact hG.comp (measurable_id.prodMk hA)
    have : (fun ω : TSOmega N => tsCounts ω (t + 1)) = F ∘ (fun ω => (ω, tsCounts ω t)) := by
      funext ω
      rfl
    rw [this]
    exact hF.comp (measurable_id.prodMk ih)

lemma tsArm_measurable (t : ℕ) : Measurable (fun ω : TSOmega N => tsArm ω t) := by
  let G : TSOmega N × ((Fin N → ℕ) × (Fin N → ℕ)) → Fin N :=
    fun p => argmaxMin (fun i => p.1.1 (i, t, p.2.1 i, p.2.2 i))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro c
    show Measurable fun x : TSOmega N => argmaxMin (fun i => x.1 (i, t, c.1 i, c.2 i))
    exact argmaxMin_measurable.comp
      (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst)
  have : (fun ω : TSOmega N => tsArm ω t) = G ∘ (fun ω => (ω, tsCounts ω t)) := by
    funext ω; rfl
  rw [this]
  exact hG.comp (measurable_id.prodMk (tsCounts_measurable t))

lemma tsPlays_eq_sum (ω : TSOmega N) (T : ℕ) (i : Fin N) :
    (tsPlays ω T i : ENNReal) = ∑ u ∈ Finset.range T, if tsArm ω u = i then 1 else 0 := by
  unfold tsPlays
  rw [Finset.card_filter]
  push_cast
  rfl

lemma tsPlays_measurable (T : ℕ) (i : Fin N) :
    Measurable (fun ω : TSOmega N => (tsPlays ω T i : ENNReal)) := by
  simp_rw [tsPlays_eq_sum]
  refine Finset.measurable_sum _ (fun u _ => ?_)
  exact Measurable.ite ((tsArm_measurable u) (measurableSet_singleton i)) measurable_const
    measurable_const

/-- Rewards supported in `[0,1]` give means in `[0,1]`. -/
lemma mean_mem (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N) :
    0 ≤ banditArmMean ν i ∧ banditArmMean ν i ≤ 1 := by
  have hae : ∀ᵐ x ∂(ν.P i), x ∈ Set.Icc (0:ℝ) 1 := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff (μ := ν.P i) measurableSet_Icc).mpr (hsupp i)
    simpa [Set.compl_def] using this
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun x hx => hx.1)
  · have h := integral_mono_of_nonneg (μ := ν.P i) (f := fun x => x) (g := fun _ => (1:ℝ))
      (hae.mono fun x hx => hx.1) (integrable_const 1) (hae.mono fun x hx => hx.2)
    unfold banditArmMean
    simpa using h

lemma optimal_eq (ν : StochasticBandit N)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) :
    banditOptimalMean ν = banditArmMean ν 0 := by
  unfold banditOptimalMean
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    by_cases h : i = 0
    · rw [h]
    · exact (hopt i h).le
  · exact le_ciSup (Set.finite_range _).bddAbove 0

lemma gap_eq (ν : StochasticBandit N)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (i : Fin N) :
    banditGap ν i = gapTo0 ν i := by
  unfold banditGap gapTo0; rw [optimal_eq ν hopt]

lemma regret_pointwise (ν : StochasticBandit N)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T : ℕ) (ω : TSOmega N) :
    ∑ t ∈ Finset.range T, ENNReal.ofReal (banditGap ν (tsArm ω t)) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
        ENNReal.ofReal (gapTo0 ν a) * (tsPlays ω T a : ENNReal) := by
  rw [← Finset.sum_fiberwise (Finset.range T) (fun t => tsArm ω t)
    (fun t => ENNReal.ofReal (banditGap ν (tsArm ω t)))]
  rw [Finset.sum_filter_of_ne]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]),
      Finset.sum_const, nsmul_eq_mul, gap_eq ν hopt, mul_comm]
    rfl
  · intro a _ hne h0
    apply hne
    rw [h0]
    simp [gapTo0]

/-- D0: the regret is the gap-weighted sum of expected plays. -/
lemma regret_eq (ν : StochasticBandit N)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T : ℕ) :
    tsRegret ν T = ∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
      ENNReal.ofReal (gapTo0 ν a) * ∫⁻ ω, (tsPlays ω T a : ENNReal) ∂(tsLaw ν) := by
  unfold tsRegret
  simp_rw [regret_pointwise ν hopt T]
  rw [lintegral_finsetSum _ (fun a _ => (tsPlays_measurable T a).const_mul _)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [lintegral_const_mul _ (tsPlays_measurable T a)]



lemma tsPlays_mono (ω : TSOmega N) (i : Fin N) {t t' : ℕ} (h : t ≤ t') :
    tsPlays ω t i ≤ tsPlays ω t' i := by
  unfold tsPlays
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

instance tsLaw_prob (ν : StochasticBandit N) : IsProbabilityMeasure (tsLaw ν) := by
  unfold tsLaw
  infer_instance

/-! ## Generic coordinate refresh for `Measure.infinitePi` -/

lemma upd_map_gen {ι β : Type*} [Countable ι] [DecidableEq ι] [MeasurableSpace β]
    (m : ι → Measure β) [∀ i, IsProbabilityMeasure (m i)] (k0 : ι) :
    ((m k0).prod (Measure.infinitePi m)).map (fun p => Function.update p.2 k0 p.1) =
      Measure.infinitePi m := by
  have hmeas : Measurable (fun p : β × (ι → β) => Function.update p.2 k0 p.1) :=
    measurable_update'.comp measurable_swap
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hk : k0 ∈ s
  · have : (fun p : β × (ι → β) => Function.update p.2 k0 p.1) ⁻¹' (Set.pi (↑s) t) =
        t k0 ×ˢ Set.pi (↑(s.erase k0)) t := by
      ext ⟨c, w⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨by simpa using h k0 hk, fun i ⟨hne, hi⟩ => ?_⟩
        simpa [Function.update_of_ne hne] using h i hi
      · rintro ⟨h1, h2⟩ i hi
        by_cases hik : i = k0
        · subst hik
          simpa using h1
        · simpa [Function.update_of_ne hik] using h2 i ⟨hik, hi⟩
    rw [this, Measure.prod_prod, Measure.infinitePi_pi m (fun i _ => ht i)]
    exact Finset.mul_prod_erase s (fun i => m i (t i)) hk
  · have : (fun p : β × (ι → β) => Function.update p.2 k0 p.1) ⁻¹' (Set.pi (↑s) t) =
        Set.univ ×ˢ Set.pi (↑s) t := by
      ext ⟨c, w⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
        Set.mem_univ, true_and]
      refine forall₂_congr fun i hi => ?_
      have hik : i ≠ k0 := fun h => hk (h ▸ hi)
      simp [Function.update_of_ne hik]
    rw [this, Measure.prod_prod, Measure.infinitePi_pi m (fun i _ => ht i), measure_univ, one_mul]

lemma upd_lintegral {ι β : Type*} [Countable ι] [DecidableEq ι] [MeasurableSpace β]
    (m : ι → Measure β) [∀ i, IsProbabilityMeasure (m i)] (k0 : ι)
    (F : (ι → β) → ENNReal) (hF : Measurable F) :
    ∫⁻ w, F w ∂(Measure.infinitePi m) =
      ∫⁻ w, ∫⁻ b, F (Function.update w k0 b) ∂(m k0) ∂(Measure.infinitePi m) := by
  have hmeas : Measurable (fun p : β × (ι → β) => Function.update p.2 k0 p.1) :=
    measurable_update'.comp measurable_swap
  conv_lhs => rw [← upd_map_gen m k0]
  rw [lintegral_map hF hmeas, lintegral_prod (fun p : β × (ι → β) => F (Function.update p.2 k0 p.1))
    (hF.comp hmeas).aemeasurable]
  exact lintegral_lintegral_swap (f := fun b w => F (Function.update w k0 b))
    (hF.comp hmeas).aemeasurable

/-! ## Freshness of the coin of round `u` -/

/-- The coin table entry `(X(k0), V(k0))` is independent of everything that does not read it. -/
lemma fresh_coin (ν : StochasticBandit N) (k0 : Fin N × ℕ)
    (g : ℝ → unitInterval → ENNReal) (hg : Measurable (Function.uncurry g))
    (H : TSOmega N → ENNReal) (hH : Measurable H)
    (hinv : ∀ (a : ℝ) (b : unitInterval) (ω : TSOmega N),
      H (ω.1, Function.update ω.2.1 k0 a, Function.update ω.2.2 k0 b) = H ω) :
    ∫⁻ ω, g (ω.2.1 k0) (ω.2.2 k0) * H ω ∂(tsLaw ν) =
      (∫⁻ a, ∫⁻ b, g a b ∂(volume : Measure unitInterval) ∂(ν.P k0.1)) *
        ∫⁻ ω, H ω ∂(tsLaw ν) := by
  set μW := Measure.infinitePi
    (fun k : Fin N × ℕ × ℕ × ℕ => betaMeasure ((k.2.2.1 : ℝ) + 1) ((k.2.2.2 : ℝ) + 1))
  set μX := Measure.infinitePi (fun k : Fin N × ℕ => ν.P k.1)
  set μV := Measure.infinitePi (fun _ : Fin N × ℕ => (volume : Measure unitInterval))
  have hlaw : tsLaw ν = μW.prod (μX.prod μV) := rfl
  have hga : ∀ a, Measurable (g a) := fun a => hg.comp (measurable_const.prodMk measurable_id)
  set ψ : ℝ → ENNReal := fun a => ∫⁻ b, g a b ∂(volume : Measure unitInterval)
  have hψ : Measurable ψ := hg.lintegral_prod_right'
  have hGm : Measurable (fun ω : TSOmega N => g (ω.2.1 k0) (ω.2.2 k0)) := by
    have : (fun ω : TSOmega N => g (ω.2.1 k0) (ω.2.2 k0)) =
        Function.uncurry g ∘ (fun ω : TSOmega N => (ω.2.1 k0, ω.2.2 k0)) := rfl
    rw [this]
    exact hg.comp (((measurable_pi_apply k0).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply k0).comp (measurable_snd.comp measurable_snd)))
  have hHinvV : ∀ w x v (b : unitInterval), H (w, x, Function.update v k0 b) = H (w, x, v) := by
    intro w x v b
    have := hinv (x k0) b (w, x, v)
    simpa [Function.update_eq_self] using this
  have hHinvX : ∀ w x v (a : ℝ), H (w, Function.update x k0 a, v) = H (w, x, v) := by
    intro w x v a
    have := hinv a (v k0) (w, x, v)
    simpa [Function.update_eq_self] using this
  rw [hlaw, lintegral_prod (fun ω : TSOmega N => g (ω.2.1 k0) (ω.2.2 k0) * H ω)
    (hGm.mul hH).aemeasurable, lintegral_prod (fun ω : TSOmega N => H ω) hH.aemeasurable,
    ← lintegral_const_mul _ (hH.lintegral_prod_right')]
  refine lintegral_congr (fun w => ?_)
  have hHw : Measurable (fun p : (Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval) => H (w, p)) :=
    hH.comp measurable_prodMk_left
  have hGw : Measurable (fun p : (Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval) =>
      g (p.1 k0) (p.2 k0) * H (w, p)) := (hGm.mul hH).comp measurable_prodMk_left
  rw [lintegral_prod (fun p : (Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval) =>
      g (p.1 k0) (p.2 k0) * H (w, p)) hGw.aemeasurable,
    lintegral_prod (fun p : (Fin N × ℕ → ℝ) × (Fin N × ℕ → unitInterval) => H (w, p))
      hHw.aemeasurable]
  have hv : ∀ x : Fin N × ℕ → ℝ, ∫⁻ v, g (x k0) (v k0) * H (w, x, v) ∂μV =
      ψ (x k0) * ∫⁻ v, H (w, x, v) ∂μV := by
    intro x
    have hFm : Measurable (fun v : Fin N × ℕ → unitInterval => g (x k0) (v k0) * H (w, x, v)) :=
      ((hga (x k0)).comp (measurable_pi_apply k0)).mul
        (hH.comp (measurable_prodMk_left.comp measurable_prodMk_left))
    rw [upd_lintegral _ k0 _ hFm]
    simp_rw [Function.update_self, hHinvV]
    simp_rw [lintegral_mul_const _ (hga (x k0))]
    exact lintegral_const_mul _ (hH.comp (measurable_prodMk_left.comp measurable_prodMk_left))
  simp_rw [hv]
  have hK : Measurable (fun x : Fin N × ℕ → ℝ => ∫⁻ v, H (w, x, v) ∂μV) :=
    hHw.lintegral_prod_right'
  have hF2 : Measurable (fun x : Fin N × ℕ → ℝ => ψ (x k0) * ∫⁻ v, H (w, x, v) ∂μV) :=
    (hψ.comp (measurable_pi_apply k0)).mul hK
  have hU := upd_lintegral (fun k : Fin N × ℕ => ν.P k.1) k0 _ hF2
  refine hU.trans ?_
  simp_rw [Function.update_self, hHinvX]
  simp_rw [lintegral_mul_const _ hψ]
  exact lintegral_const_mul _ hK

/-! ## Locality: rounds `≤ u` never read the coin entry of round `u` -/

def updC (k0 : Fin N × ℕ) (a : ℝ) (b : unitInterval) (ω : TSOmega N) : TSOmega N :=
  (ω.1, Function.update ω.2.1 k0 a, Function.update ω.2.2 k0 b)

lemma tsCounts_updC (k0 : Fin N × ℕ) (a : ℝ) (b : unitInterval) (ω : TSOmega N) :
    ∀ t, t ≤ k0.2 → tsCounts (updC k0 a b ω) t = tsCounts ω t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have harm : tsArm (updC k0 a b ω) t = tsArm ω t := by
      unfold tsArm tsTheta tsSuccesses tsFailures
      rw [ih']
      rfl
    have hne : (tsArm ω t, t) ≠ k0 := by
      intro h
      have := congrArg Prod.snd h
      simp at this
      omega
    rw [tsCounts_succ', tsCounts_succ', harm, ih']
    simp only [updC, Function.update_of_ne hne]

lemma tsArm_updC (k0 : Fin N × ℕ) (a : ℝ) (b : unitInterval) (ω : TSOmega N) :
    tsArm (updC k0 a b ω) k0.2 = tsArm ω k0.2 := by
  unfold tsArm tsTheta tsSuccesses tsFailures
  rw [tsCounts_updC k0 a b ω k0.2 le_rfl]
  rfl

/-! ## Monotonicity of the counts -/

lemma S_succ_ge (ω : TSOmega N) (t : ℕ) (i : Fin N) :
    (tsCounts ω t).1 i ≤ (tsCounts ω (t + 1)).1 i ∧ (tsCounts ω t).2 i ≤ (tsCounts ω (t + 1)).2 i := by
  rw [tsCounts_succ']
  by_cases ha : tsArm ω t = i
  · subst ha
    split_ifs <;> simp
  · split_ifs <;> simp [Function.update_of_ne (Ne.symm ha)]

lemma S_mono (ω : TSOmega N) (i : Fin N) {t t' : ℕ} (h : t ≤ t') :
    (tsCounts ω t).1 i ≤ (tsCounts ω t').1 i ∧ (tsCounts ω t).2 i ≤ (tsCounts ω t').2 i := by
  induction h with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | step _ ih => exact ⟨ih.1.trans (S_succ_ge ω _ i).1, ih.2.trans (S_succ_ge ω _ i).2⟩

lemma S_eq_of_plays_eq (ω : TSOmega N) (i : Fin N) {t t' : ℕ} (h : t ≤ t')
    (hp : tsPlays ω t i = tsPlays ω t' i) : (tsCounts ω t).1 i = (tsCounts ω t').1 i := by
  have h1 := S_mono ω i h
  rw [tsPlays_eq, tsPlays_eq] at hp
  omega

/-! ## Optional skipping for the coins of arm `i` -/

/-- `Q i k s`: arm `i` completes `k` plays, with `s` successes among them. -/
def Qset (i : Fin N) (k s : ℕ) : Set (TSOmega N) :=
  {ω | ∃ u, tsPlays ω u i = k ∧ (tsCounts ω u).1 i = s}

/-- `A i u k s`: at round `u` arm `i` has `k` plays with `s` successes and is played. -/
def Aset (i : Fin N) (u k s : ℕ) : Set (TSOmega N) :=
  {ω | tsPlays ω u i = k ∧ (tsCounts ω u).1 i = s ∧ tsArm ω u = i}

lemma Aset_meas (i : Fin N) (u k s : ℕ) : MeasurableSet (Aset (N := N) i u k s) := by
  refine mset_factor ((tsCounts_measurable u).prodMk (tsArm_measurable u))
    (fun ω => ω ∈ Aset i u k s) ?_
  intro ω ω' h hω
  have h1 : tsCounts ω u = tsCounts ω' u := congrArg Prod.fst h
  have h2 : tsArm ω u = tsArm ω' u := congrArg Prod.snd h
  obtain ⟨a1, a2, a3⟩ := hω
  refine ⟨?_, ?_, ?_⟩
  · rw [tsPlays_eq] at a1 ⊢; rw [← h1]; exact a1
  · rw [← h1]; exact a2
  · rw [← h2]; exact a3

lemma Aset_inv (i : Fin N) (u k s : ℕ) (a : ℝ) (b : unitInterval) (ω : TSOmega N) :
    updC (i, u) a b ω ∈ Aset i u k s ↔ ω ∈ Aset i u k s := by
  have h1 := tsCounts_updC (i, u) a b ω u le_rfl
  have h2 := tsArm_updC (i, u) a b ω
  simp only [Aset, Set.mem_setOf_eq, tsPlays_eq, h1]
  rw [show tsArm (updC (i, u) a b ω) u = tsArm ω u from h2]

lemma Aset_disj (i : Fin N) (k s : ℕ) :
    Pairwise (fun u v => Disjoint (Aset (N := N) i u k s) (Aset i v k s)) := by
  intro u v huv
  rw [Set.disjoint_left]
  rintro ω ⟨hu1, _, hu3⟩ ⟨hv1, _, hv3⟩
  rcases lt_or_gt_of_ne huv with h | h
  · have := tsPlays_mono ω i (Nat.succ_le_of_lt h)
    rw [tsPlays_succ, if_pos hu3] at this
    omega
  · have := tsPlays_mono ω i (Nat.succ_le_of_lt h)
    rw [tsPlays_succ, if_pos hv3] at this
    omega

lemma Aset_sub (i : Fin N) (u k s : ℕ) : Aset (N := N) i u k s ⊆ Qset i k s := by
  rintro ω ⟨h1, h2, _⟩
  exact ⟨u, h1, h2⟩

lemma tsPlays_zero (ω : TSOmega N) (i : Fin N) : tsPlays ω 0 i = 0 := by
  simp [tsPlays]

/-- The (k+1)-th play of arm `i` happens at some round `u`. -/
lemma Qset_succ_sub (i : Fin N) (k s : ℕ) :
    Qset (N := N) i (k + 1) s ⊆
      (⋃ u, Aset i u k (s - 1) ∩ {ω | 1 ≤ s ∧ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))}) ∪
      (⋃ u, Aset i u k s ∩ {ω | ¬ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))}) := by
  classical
  rintro ω ⟨u', hu'1, hu'2⟩
  have hex : ∃ v, tsPlays ω v i = k + 1 := ⟨u', hu'1⟩
  obtain ⟨v, hvspec, hvmin⟩ : ∃ v, tsPlays ω v i = k + 1 ∧ ∀ w < v, tsPlays ω w i ≠ k + 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun w hw => Nat.find_min hex hw⟩
  have hvle : v ≤ u' := by
    by_contra hlt
    exact hvmin u' (by omega) hu'1
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · rw [h0, tsPlays_zero] at hvspec; omega
    · exact ⟨v - 1, by omega⟩
  have hmin : tsPlays ω u i ≠ k + 1 := hvmin u (by omega)
  have hstep := tsPlays_succ ω u i
  have harm : tsArm ω u = i := by
    by_contra hne
    rw [if_neg hne] at hstep
    omega
  rw [if_pos harm] at hstep
  have hk : tsPlays ω u i = k := by omega
  have hS : (tsCounts ω (u + 1)).1 i = s := by
    rw [← hu'2]
    exact S_eq_of_plays_eq ω i hvle (by rw [hvspec, hu'1])
  have hS' := tsCounts_succ' ω u
  rw [harm] at hS'
  by_cases hc : ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))
  · rw [if_pos hc] at hS'
    rw [hS'] at hS
    simp at hS
    left
    refine Set.mem_iUnion.mpr ⟨u, ⟨hk, by omega, harm⟩, by omega, hc⟩
  · rw [if_neg hc] at hS'
    rw [hS'] at hS
    simp at hS
    right
    exact Set.mem_iUnion.mpr ⟨u, ⟨hk, hS, harm⟩, hc⟩

/-- Integrals of the coin indicator against the arm law. -/
lemma coin_succ_int (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N) :
    ∫⁻ a, ∫⁻ b, (if ((b : ℝ) < a) then (1 : ENNReal) else 0) ∂(volume : Measure unitInterval)
      ∂(ν.P i) = ENNReal.ofReal (banditArmMean ν i) := by
  have hae : ∀ᵐ x ∂(ν.P i), x ∈ Set.Icc (0:ℝ) 1 := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff (μ := ν.P i) measurableSet_Icc).mpr (hsupp i)
    simpa [Set.compl_def] using this
  have hpt : ∀ a ∈ Set.Icc (0:ℝ) 1,
      ∫⁻ b, (if ((b : ℝ) < a) then (1 : ENNReal) else 0) ∂(volume : Measure unitInterval) =
        ENNReal.ofReal a := by
    intro a ha
    have hset : {b : unitInterval | (b : ℝ) < a} = Set.Iio ⟨a, ha⟩ := by
      ext b; simp [Subtype.mk_lt_mk, ← Subtype.coe_lt_coe]
    have : (fun b : unitInterval => if ((b : ℝ) < a) then (1 : ENNReal) else 0) =
        Set.indicator {b : unitInterval | (b : ℝ) < a} 1 := by
      funext b; simp [Set.indicator]
    rw [this, lintegral_indicator_one (by rw [hset]; exact measurableSet_Iio), hset,
      unitInterval.volume_Iio]
  rw [lintegral_congr_ae (hae.mono fun a ha => hpt a ha)]
  unfold banditArmMean
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable hae
  · exact hae.mono fun x hx => hx.1

lemma coin_fail_int (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N) :
    ∫⁻ a, ∫⁻ b, (if ¬ ((b : ℝ) < a) then (1 : ENNReal) else 0) ∂(volume : Measure unitInterval)
      ∂(ν.P i) = ENNReal.ofReal (1 - banditArmMean ν i) := by
  have hsum : ∀ a : ℝ, ∫⁻ b, (if ¬ ((b : ℝ) < a) then (1 : ENNReal) else 0)
      ∂(volume : Measure unitInterval) =
      1 - ∫⁻ b, (if ((b : ℝ) < a) then (1 : ENNReal) else 0) ∂(volume : Measure unitInterval) := by
    intro a
    have hm : MeasurableSet {b : unitInterval | (b : ℝ) < a} :=
      measurableSet_lt measurable_subtype_coe measurable_const
    have e1 : (fun b : unitInterval => if ((b : ℝ) < a) then (1 : ENNReal) else 0) =
        Set.indicator {b : unitInterval | (b : ℝ) < a} 1 := by
      funext b; simp [Set.indicator]
    have e2 : (fun b : unitInterval => if ¬ ((b : ℝ) < a) then (1 : ENNReal) else 0) =
        Set.indicator {b : unitInterval | (b : ℝ) < a}ᶜ 1 := by
      funext b; simp [Set.indicator]
    rw [e1, e2, lintegral_indicator_one hm, lintegral_indicator_one hm.compl, prob_compl_eq_one_sub hm]
  simp_rw [hsum]
  have hm := mean_mem ν hsupp i
  have hmeas : Measurable (fun a : ℝ => ∫⁻ b, (if ((b : ℝ) < a) then (1 : ENNReal) else 0)
      ∂(volume : Measure unitInterval)) := by
    have : Measurable (Function.uncurry (fun (a : ℝ) (b : unitInterval) =>
        (if ((b : ℝ) < a) then (1 : ENNReal) else 0))) :=
      Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_fst)
        measurable_const measurable_const
    exact this.lintegral_prod_right'
  rw [lintegral_sub hmeas (by rw [coin_succ_int ν hsupp i]; exact ENNReal.ofReal_ne_top)
    (Filter.Eventually.of_forall fun a => by
      simp only [Pi.one_apply]
      calc _ ≤ ∫⁻ b, (1 : ENNReal) ∂(volume : Measure unitInterval) :=
            lintegral_mono fun b => by split_ifs <;> simp
        _ = 1 := by simp),
    lintegral_const, measure_univ, mul_one, coin_succ_int ν hsupp i,
    ENNReal.ofReal_sub _ hm.1, ENNReal.ofReal_one]

lemma prob_A_coin (ν : StochasticBandit N) (i : Fin N) (u k s : ℕ) (c : Prop) [Decidable c]
    (P : ℝ → unitInterval → Prop) [∀ a b, Decidable (P a b)]
    (hP : Measurable (Function.uncurry (fun (a : ℝ) (b : unitInterval) =>
      (if P a b then (1 : ENNReal) else 0)))) :
    tsLaw ν (Aset i u k s ∩ {ω | c ∧ P (ω.2.1 (i, u)) (ω.2.2 (i, u))}) ≤
      (∫⁻ a, ∫⁻ b, (if P a b then (1 : ENNReal) else 0) ∂(volume : Measure unitInterval)
        ∂(ν.P i)) * tsLaw ν (Aset i u k s) := by
  have hA := Aset_meas (N := N) i u k s
  have hle : (Aset i u k s ∩ {ω | c ∧ P (ω.2.1 (i, u)) (ω.2.2 (i, u))}) ⊆
      {ω | P (ω.2.1 (i, u)) (ω.2.2 (i, u))} ∩ Aset i u k s := by
    rintro ω ⟨h1, _, h2⟩; exact ⟨h2, h1⟩
  refine (measure_mono hle).trans (le_of_eq ?_)
  have key := fresh_coin ν (i, u) (fun a b => if P a b then (1 : ENNReal) else 0) hP
    ((Aset i u k s).indicator 1) (measurable_one.indicator hA) (by
      intro a b ω
      change (Aset i u k s).indicator 1 (updC (i, u) a b ω) = (Aset i u k s).indicator 1 ω
      by_cases h : ω ∈ Aset i u k s
      · rw [Set.indicator_of_mem ((Aset_inv i u k s a b ω).mpr h), Set.indicator_of_mem h]; rfl
      · rw [Set.indicator_of_notMem (mt (Aset_inv i u k s a b ω).mp h),
          Set.indicator_of_notMem h])
  rw [← lintegral_indicator_one hA, ← key]
  have hmP : MeasurableSet {ω : TSOmega N | P (ω.2.1 (i, u)) (ω.2.2 (i, u))} := by
    have hm : Measurable (fun ω : TSOmega N => (ω.2.1 (i, u), ω.2.2 (i, u))) :=
      ((measurable_pi_apply (i, u)).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply (i, u)).comp (measurable_snd.comp measurable_snd))
    have : {ω : TSOmega N | P (ω.2.1 (i, u)) (ω.2.2 (i, u))} =
        (fun ω : TSOmega N => (ω.2.1 (i, u), ω.2.2 (i, u))) ⁻¹'
          ((Function.uncurry (fun (a : ℝ) (b : unitInterval) =>
            (if P a b then (1 : ENNReal) else 0))) ⁻¹' {1}) := by
      ext ω; simp
    rw [this]
    exact hm (hP (measurableSet_singleton 1))
  rw [← lintegral_indicator_one (hmP.inter hA)]
  refine lintegral_congr (fun ω => ?_)
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs <;> simp_all

lemma pascal (k s : ℕ) (p : ℝ) :
    AgrawalGoyalTS.TwoArmed.binomPMF (k + 1) p (s + 1) =
      p * AgrawalGoyalTS.TwoArmed.binomPMF k p s + (1 - p) * AgrawalGoyalTS.TwoArmed.binomPMF k p (s + 1) := by
  unfold AgrawalGoyalTS.TwoArmed.binomPMF
  rw [Nat.choose_succ_succ, Nat.succ_sub_succ]
  push_cast
  rcases Nat.lt_or_ge s k with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, k = s + 1 + d := ⟨k - (s + 1), by omega⟩
    have e1 : s + 1 + d - s = d + 1 := by omega
    have e2 : s + 1 + d - (s + 1) = d := by omega
    rw [e1, e2]; ring
  · rcases Nat.eq_or_lt_of_le h with h2 | h2
    · subst h2
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
      simp <;> ring
    · rw [Nat.choose_eq_zero_of_lt h2, Nat.choose_eq_zero_of_lt (by omega)]
      simp

lemma pascal0 (k : ℕ) (p : ℝ) :
    AgrawalGoyalTS.TwoArmed.binomPMF (k + 1) p 0 = (1 - p) * AgrawalGoyalTS.TwoArmed.binomPMF k p 0 := by
  unfold AgrawalGoyalTS.TwoArmed.binomPMF
  simp; ring

lemma pmf_nonneg' (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ AgrawalGoyalTS.TwoArmed.binomPMF n p k := by
  unfold AgrawalGoyalTS.TwoArmed.binomPMF
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- D5 (optional skipping): the success count of the first `k` plays of arm `i` is
stochastically controlled by `Binomial(k, μ_i)`, on the event that the plays happen. -/
theorem opt_skip (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N) :
    ∀ k s, tsLaw ν (Qset i k s) ≤
      ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν i) s) := by
  have hm := mean_mem ν hsupp i
  set μ := banditArmMean ν i
  intro k
  induction k with
  | zero =>
    intro s
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      have h1 : AgrawalGoyalTS.TwoArmed.binomPMF 0 μ 0 = 1 := by
        simp [AgrawalGoyalTS.TwoArmed.binomPMF]
      rw [h1, ENNReal.ofReal_one]
      exact prob_le_one
    · have : Qset (N := N) i 0 s = ∅ := by
        ext ω
        simp only [Qset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro u hu hs
        rw [tsPlays_eq] at hu
        omega
      rw [this, measure_empty]; exact bot_le
  | succ k ih =>
    intro s
    have hsm : Measurable (Function.uncurry (fun (a : ℝ) (b : unitInterval) =>
        (if ((b : ℝ) < a) then (1 : ENNReal) else 0))) :=
      Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_fst)
        measurable_const measurable_const
    have hfm : Measurable (Function.uncurry (fun (a : ℝ) (b : unitInterval) =>
        (if ¬ ((b : ℝ) < a) then (1 : ENNReal) else 0))) :=
      Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
        measurable_fst).compl measurable_const measurable_const
    -- sum over rounds of a disjoint family
    have hsumA : ∀ s', ∑' u, tsLaw ν (Aset i u k s') ≤ tsLaw ν (Qset i k s') := by
      intro s'
      rw [← measure_iUnion (Aset_disj i k s') (fun u => Aset_meas i u k s')]
      exact measure_mono (Set.iUnion_subset fun u => Aset_sub i u k s')
    have hsucc : tsLaw ν (⋃ u, Aset i u k (s - 1) ∩
        {ω | 1 ≤ s ∧ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))}) ≤
        (if 1 ≤ s then ENNReal.ofReal μ * tsLaw ν (Qset i k (s - 1)) else 0) := by
      split_ifs with hs
      · refine (measure_iUnion_le _).trans ?_
        calc ∑' u, tsLaw ν (Aset i u k (s - 1) ∩
              {ω | 1 ≤ s ∧ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))})
            ≤ ∑' u, ENNReal.ofReal μ * tsLaw ν (Aset i u k (s - 1)) := by
              refine ENNReal.tsum_le_tsum (fun u => ?_)
              have := prob_A_coin ν i u k (s - 1) (1 ≤ s) (fun a b => (b : ℝ) < a) hsm
              rwa [coin_succ_int ν hsupp i] at this
          _ = ENNReal.ofReal μ * ∑' u, tsLaw ν (Aset i u k (s - 1)) := ENNReal.tsum_mul_left
          _ ≤ ENNReal.ofReal μ * tsLaw ν (Qset i k (s - 1)) := by gcongr; exact hsumA _
      · have : (⋃ u, Aset (N := N) i u k (s - 1) ∩
            {ω | 1 ≤ s ∧ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))}) = ∅ := by
          ext ω; simp [hs]
        rw [this, measure_empty]
    have hfail : tsLaw ν (⋃ u, Aset i u k s ∩
        {ω | ¬ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))}) ≤
        ENNReal.ofReal (1 - μ) * tsLaw ν (Qset i k s) := by
      refine (measure_iUnion_le _).trans ?_
      calc ∑' u, tsLaw ν (Aset i u k s ∩ {ω | ¬ ((ω.2.2 (i, u) : ℝ) < ω.2.1 (i, u))})
          ≤ ∑' u, ENNReal.ofReal (1 - μ) * tsLaw ν (Aset i u k s) := by
            refine ENNReal.tsum_le_tsum (fun u => ?_)
            have := prob_A_coin ν i u k s True (fun a b => ¬ ((b : ℝ) < a)) hfm
            rw [coin_fail_int ν hsupp i] at this
            refine le_trans (measure_mono ?_) this
            rintro ω ⟨h1, h2⟩; exact ⟨h1, trivial, h2⟩
        _ = ENNReal.ofReal (1 - μ) * ∑' u, tsLaw ν (Aset i u k s) := ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal (1 - μ) * tsLaw ν (Qset i k s) := by gcongr; exact hsumA _
    refine (measure_mono (Qset_succ_sub i k s)).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hsucc hfail).trans ?_
    have h1μ : 0 ≤ 1 - μ := by linarith [hm.2]
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      simp only [show ¬ (1 ≤ 0) from by omega, if_false, zero_add]
      rw [pascal0, ENNReal.ofReal_mul h1μ]
      gcongr
      exact ih 0
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      simp only [show 1 ≤ s' + 1 from by omega, if_true, Nat.add_sub_cancel]
      rw [pascal, ENNReal.ofReal_add (mul_nonneg hm.1 (pmf_nonneg' _ _ hm.1 hm.2 _))
        (mul_nonneg h1μ (pmf_nonneg' _ _ hm.1 hm.2 _)), ENNReal.ofReal_mul hm.1,
        ENNReal.ofReal_mul h1μ]
      gcongr
      · exact ih s'
      · exact ih (s' + 1)


lemma tsTheta_measurable (t : ℕ) (j : Fin N) : Measurable (fun ω : TSOmega N => tsTheta ω t j) := by
  let G : TSOmega N × ((Fin N → ℕ) × (Fin N → ℕ)) → ℝ := fun p => p.1.1 (j, t, p.2.1 j, p.2.2 j)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro c
    show Measurable fun x : TSOmega N => x.1 (j, t, c.1 j, c.2 j)
    exact (measurable_pi_apply _).comp measurable_fst
  have : (fun ω : TSOmega N => tsTheta ω t j) = G ∘ (fun ω => (ω, tsCounts ω t)) := by
    funext ω; rfl
  rw [this]
  exact hG.comp (measurable_id.prodMk (tsCounts_measurable t))

lemma cset_meas (t : ℕ) (P : (Fin N → ℕ) × (Fin N → ℕ) → Prop) :
    MeasurableSet {ω : TSOmega N | P (tsCounts ω t)} :=
  (tsCounts_measurable t) (Set.to_countable {x | P x}).measurableSet

lemma argmaxMin_spec (θ : Fin N → ℝ) (j : Fin N) : θ j ≤ θ (argmaxMin θ) := by
  have hne : (Finset.univ.filter (fun i => ∀ j, θ j ≤ θ i)).Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ θ Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩
  unfold argmaxMin
  rw [dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2 j

lemma argmaxMin_eq_zero (θ : Fin N → ℝ) (h : ∀ j, j ≠ 0 → θ j < θ 0) : argmaxMin θ = 0 := by
  by_contra hne
  have h1 := argmaxMin_spec θ 0
  have h2 := h _ hne
  linarith

/-! ## Freshness of a posterior-sample entry `W(k0)` -/

lemma fresh_W (ν : StochasticBandit N) (k0 : Fin N × ℕ × ℕ × ℕ)
    (g : ℝ → ENNReal) (hg : Measurable g)
    (H : TSOmega N → ENNReal) (hH : Measurable H)
    (hinv : ∀ (a : ℝ) (ω : TSOmega N), H (Function.update ω.1 k0 a, ω.2) = H ω) :
    ∫⁻ ω, g (ω.1 k0) * H ω ∂(tsLaw ν) =
      (∫⁻ a, g a ∂(betaMeasure ((k0.2.2.1 : ℝ) + 1) ((k0.2.2.2 : ℝ) + 1))) *
        ∫⁻ ω, H ω ∂(tsLaw ν) := by
  set μW := Measure.infinitePi
    (fun k : Fin N × ℕ × ℕ × ℕ => betaMeasure ((k.2.2.1 : ℝ) + 1) ((k.2.2.2 : ℝ) + 1)) with hμW
  set μR := (Measure.infinitePi (fun k : Fin N × ℕ => ν.P k.1)).prod
      (Measure.infinitePi (fun _ : Fin N × ℕ => (volume : Measure unitInterval))) with hμR
  have hlaw : tsLaw ν = μW.prod μR := rfl
  have hGm : Measurable (fun ω : TSOmega N => g (ω.1 k0) * H ω) :=
    (hg.comp ((measurable_pi_apply k0).comp measurable_fst)).mul hH
  rw [hlaw, lintegral_prod_symm _ hGm.aemeasurable, lintegral_prod_symm _ hH.aemeasurable,
    ← lintegral_const_mul _ hH.lintegral_prod_left']
  refine lintegral_congr (fun r => ?_)
  have hHr : Measurable (fun w => H (w, r)) := hH.comp measurable_prodMk_right
  have hFm : Measurable (fun w : Fin N × ℕ × ℕ × ℕ → ℝ => g (w k0) * H (w, r)) :=
    (hg.comp (measurable_pi_apply k0)).mul hHr
  have hU := upd_lintegral
    (fun k : Fin N × ℕ × ℕ × ℕ => betaMeasure ((k.2.2.1 : ℝ) + 1) ((k.2.2.2 : ℝ) + 1)) k0 _ hFm
  refine hU.trans ?_
  have hinv' : ∀ w b, H (Function.update w k0 b, r) = H (w, r) := fun w b => hinv b (w, r)
  simp_rw [Function.update_self, hinv', lintegral_mul_const _ hg]
  exact lintegral_const_mul _ hHr

lemma tsCounts_updW (k0 : Fin N × ℕ × ℕ × ℕ) (a : ℝ) (ω : TSOmega N) :
    ∀ t, t ≤ k0.2.1 → tsCounts (Function.update ω.1 k0 a, ω.2) t = tsCounts ω t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have harm : tsArm (Function.update ω.1 k0 a, ω.2) t = tsArm ω t := by
      unfold tsArm tsTheta tsSuccesses tsFailures
      rw [ih']
      congr 1
      funext j
      have hne : (j, t, (tsCounts ω t).1 j, (tsCounts ω t).2 j) ≠ k0 := by
        intro h
        have := congrArg (fun p => p.2.1) h
        simp at this
        omega
      exact Function.update_of_ne hne _ _
    rw [tsCounts_succ', tsCounts_succ', harm, ih']

lemma theta_updW_ne (k0 : Fin N × ℕ × ℕ × ℕ) (a : ℝ) (ω : TSOmega N) (j : Fin N)
    (hj : j ≠ k0.1) :
    tsTheta (Function.update ω.1 k0 a, ω.2) k0.2.1 j = tsTheta ω k0.2.1 j := by
  unfold tsTheta tsSuccesses tsFailures
  rw [tsCounts_updW k0 a ω _ le_rfl]
  have hne : (j, k0.2.1, (tsCounts ω k0.2.1).1 j, (tsCounts ω k0.2.1).2 j) ≠ k0 := by
    intro h; exact hj (congrArg Prod.fst h)
  exact Function.update_of_ne hne _ _

/-- `P({W(k0) ∈ B} ∩ S) = Beta(B) P(S)` for `S` not reading `W(k0)`. -/
lemma meas_inter_eq (ν : StochasticBandit N) (k0 : Fin N × ℕ × ℕ × ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (S : Set (TSOmega N)) (hS : MeasurableSet S)
    (hinv : ∀ (a : ℝ) (ω : TSOmega N), (Function.update ω.1 k0 a, ω.2) ∈ S ↔ ω ∈ S) :
    tsLaw ν ({ω | ω.1 k0 ∈ B} ∩ S) =
      betaMeasure ((k0.2.2.1 : ℝ) + 1) ((k0.2.2.2 : ℝ) + 1) B * tsLaw ν S := by
  have hBm : MeasurableSet {ω : TSOmega N | ω.1 k0 ∈ B} :=
    ((measurable_pi_apply k0).comp measurable_fst) hB
  have key := fresh_W ν k0 (B.indicator 1) (measurable_one.indicator hB) (S.indicator 1)
    (measurable_one.indicator hS) (by
      intro a ω
      by_cases h : ω ∈ S
      · rw [Set.indicator_of_mem ((hinv a ω).mpr h), Set.indicator_of_mem h]; rfl
      · rw [Set.indicator_of_notMem (mt (hinv a ω).mp h), Set.indicator_of_notMem h])
  rw [lintegral_indicator_one hB, lintegral_indicator_one hS] at key
  rw [← key, ← lintegral_indicator_one (hBm.inter hS)]
  refine lintegral_congr (fun ω => ?_)
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs <;> simp_all

/-- Round-`t` law of `θ_i(t)` given the counts of arm `i`. -/
lemma roundB (ν : StochasticBandit N) (i : Fin N) (y : ℝ) (t a b : ℕ) :
    tsLaw ν {ω | (tsCounts ω t).1 i = a ∧ (tsCounts ω t).2 i = b ∧ y < tsTheta ω t i} =
      betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Ioi y) *
        tsLaw ν {ω | (tsCounts ω t).1 i = a ∧ (tsCounts ω t).2 i = b} := by
  have h := meas_inter_eq ν (i, t, a, b) (Set.Ioi y) measurableSet_Ioi
    {ω | (tsCounts ω t).1 i = a ∧ (tsCounts ω t).2 i = b}
    (cset_meas t (fun c => c.1 i = a ∧ c.2 i = b)) (by
      intro a' ω
      simp only [Set.mem_setOf_eq]
      rw [tsCounts_updW (i, t, a, b) a' ω t le_rfl])
  rw [← h]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2⟩
    have : tsTheta ω t i = ω.1 (i, t, a, b) := by
      unfold tsTheta tsSuccesses tsFailures; rw [h1, h2]
    rwa [← this]
  · rintro ⟨h3, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have : tsTheta ω t i = ω.1 (i, t, a, b) := by
      unfold tsTheta tsSuccesses tsFailures; rw [h1, h2]
    rwa [this]

/-- Per-round comparison (C): plays of a suboptimal arm `i` with `θ_i(t) ≤ y` against plays of arm `0`. -/
lemma roundC (ν : StochasticBandit N) (i : Fin N) (y : ℝ) (t s f : ℕ) :
    betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Ioi y) *
      tsLaw ν {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y ∧ (tsCounts ω t).1 0 = s ∧
        (tsCounts ω t).2 0 = f} ≤
    betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Iic y) *
      tsLaw ν {ω | tsArm ω t = 0 ∧ (tsCounts ω t).1 0 = s ∧ (tsCounts ω t).2 0 = f} := by
  set k0 : Fin N × ℕ × ℕ × ℕ := (0, t, s, f) with hk0
  set Hs : Set (TSOmega N) := {ω | (tsCounts ω t).1 0 = s ∧ (tsCounts ω t).2 0 = f ∧
    ∀ j : Fin N, j ≠ 0 → tsTheta ω t j ≤ y} with hHs
  have hjm : ∀ j : Fin N, MeasurableSet {ω : TSOmega N | j ≠ 0 → tsTheta ω t j ≤ y} := by
    intro j
    by_cases hj : j = 0
    · simp [hj]
    · simp only [ne_eq, hj, not_false_eq_true, forall_const]
      exact measurableSet_le (tsTheta_measurable t j) measurable_const
  have hHm : MeasurableSet Hs := by
    have h1 := cset_meas (N := N) t (fun c => c.1 0 = s ∧ c.2 0 = f)
    have h2 : MeasurableSet {ω : TSOmega N | ∀ j : Fin N, j ≠ 0 → tsTheta ω t j ≤ y} := by
      rw [Set.setOf_forall]; exact MeasurableSet.iInter hjm
    have : Hs = {ω : TSOmega N | (tsCounts ω t).1 0 = s ∧ (tsCounts ω t).2 0 = f} ∩
        {ω : TSOmega N | ∀ j : Fin N, j ≠ 0 → tsTheta ω t j ≤ y} := by
      ext ω; simp [hHs, and_assoc]
    rw [this]; exact h1.inter h2
  have hinv : ∀ (a : ℝ) (ω : TSOmega N), (Function.update ω.1 k0 a, ω.2) ∈ Hs ↔ ω ∈ Hs := by
    intro a ω
    simp only [hHs, Set.mem_setOf_eq]
    rw [tsCounts_updW k0 a ω t le_rfl]
    have : ∀ j : Fin N, j ≠ 0 → tsTheta (Function.update ω.1 k0 a, ω.2) t j = tsTheta ω t j :=
      fun j hj => theta_updW_ne k0 a ω j hj
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj => (this j hj) ▸ h3 j hj⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj => (this j hj).symm ▸ h3 j hj⟩
  have hθ0 : ∀ ω : TSOmega N, (tsCounts ω t).1 0 = s → (tsCounts ω t).2 0 = f →
      tsTheta ω t 0 = ω.1 k0 := by
    intro ω h1 h2; unfold tsTheta tsSuccesses tsFailures; rw [h1, h2]
  have e1 := meas_inter_eq ν k0 (Set.Iic y) measurableSet_Iic Hs hHm hinv
  have e2 := meas_inter_eq ν k0 (Set.Ioi y) measurableSet_Ioi Hs hHm hinv
  have sub1 : {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y ∧ (tsCounts ω t).1 0 = s ∧
      (tsCounts ω t).2 0 = f} ⊆ {ω : TSOmega N | ω.1 k0 ∈ Set.Iic y} ∩ Hs := by
    rintro ω ⟨ha, hy, h1, h2⟩
    have hall : ∀ j, tsTheta ω t j ≤ y := fun j => by
      have := argmaxMin_spec (tsTheta ω t) j
      unfold tsArm at ha
      rw [ha] at this
      linarith
    refine ⟨?_, h1, h2, fun j _ => hall j⟩
    show ω.1 k0 ≤ y
    rw [← hθ0 ω h1 h2]; exact hall 0
  have sub2 : {ω : TSOmega N | ω.1 k0 ∈ Set.Ioi y} ∩ Hs ⊆
      {ω | tsArm ω t = 0 ∧ (tsCounts ω t).1 0 = s ∧ (tsCounts ω t).2 0 = f} := by
    rintro ω ⟨hy, h1, h2, h3⟩
    refine ⟨?_, h1, h2⟩
    have hy' : y < tsTheta ω t 0 := by rw [hθ0 ω h1 h2]; exact hy
    exact argmaxMin_eq_zero _ (fun j hj => lt_of_le_of_lt (h3 j hj) hy')
  calc betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Ioi y) *
        tsLaw ν {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y ∧ (tsCounts ω t).1 0 = s ∧
          (tsCounts ω t).2 0 = f}
      ≤ betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Ioi y) *
          (betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Iic y) * tsLaw ν Hs) := by
        gcongr; rw [← e1]; exact measure_mono sub1
    _ = betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Iic y) *
          (betaMeasure ((s : ℝ) + 1) ((f : ℝ) + 1) (Set.Ioi y) * tsLaw ν Hs) := by ring
    _ ≤ _ := by gcongr; rw [← e2]; exact measure_mono sub2


/-! ## Per-arm sums -/

lemma pmf_sum' (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), AgrawalGoyalTS.TwoArmed.binomPMF n p k = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold AgrawalGoyalTS.TwoArmed.binomPMF; ring

lemma tsPlays_le (ω : TSOmega N) (t : ℕ) (i : Fin N) : tsPlays ω t i ≤ t := by
  unfold tsPlays
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma sum_Aset_le (ν : StochasticBandit N) (i : Fin N) (T k s : ℕ) :
    ∑ t ∈ Finset.range T, tsLaw ν (Aset i t k s) ≤ tsLaw ν (Qset i k s) := by
  rw [← measure_biUnion_finset ((Aset_disj i k s).set_pairwise _) (fun u _ => Aset_meas i u k s)]
  exact measure_mono (Set.iUnion₂_subset fun u _ => Aset_sub i u k s)

lemma plays_lintegral (ν : StochasticBandit N) (T : ℕ) (i : Fin N) :
    ∫⁻ ω, (tsPlays ω T i : ENNReal) ∂(tsLaw ν) =
      ∑ t ∈ Finset.range T, tsLaw ν {ω | tsArm ω t = i} := by
  simp_rw [tsPlays_eq_sum]
  have hmeas : ∀ u ∈ Finset.range T,
      Measurable (fun ω : TSOmega N => if tsArm ω u = i then (1 : ENNReal) else 0) :=
    fun u _ => Measurable.ite ((tsArm_measurable u) (measurableSet_singleton i))
      measurable_const measurable_const
  rw [lintegral_finset_sum _ hmeas]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hm : MeasurableSet {ω : TSOmega N | tsArm ω t = i} :=
    (tsArm_measurable t) (measurableSet_singleton i)
  rw [← lintegral_indicator_one hm]
  refine lintegral_congr (fun ω => ?_)
  simp [Set.indicator]

/-- (A): plays at which the empirical mean is too high. -/
lemma termA (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N)
    (x : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, tsLaw ν {ω | tsArm ω t = i ∧
        x * (tsPlays ω t i : ℝ) < ((tsCounts ω t).1 i : ℝ)} ≤
      ∑ k ∈ Finset.range T, ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
        ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν i) s) := by
  calc _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range T,
        ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
          tsLaw ν (Aset i t k s) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        have hsub : {ω | tsArm ω t = i ∧ x * (tsPlays ω t i : ℝ) < ((tsCounts ω t).1 i : ℝ)} ⊆
            ⋃ k ∈ Finset.range T,
              ⋃ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
                Aset i t k s := by
          rintro ω ⟨ha, hx⟩
          simp only [Set.mem_iUnion, exists_prop, Finset.mem_range, Finset.mem_filter]
          refine ⟨tsPlays ω t i, lt_of_le_of_lt (tsPlays_le ω t i) (Finset.mem_range.mp ht),
            (tsCounts ω t).1 i, ⟨?_, hx⟩, rfl, rfl, ha⟩
          rw [tsPlays_eq]; omega
        exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _))
    _ = ∑ k ∈ Finset.range T,
          ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
            ∑ t ∈ Finset.range T, tsLaw ν (Aset i t k s) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ ≤ _ := by
        gcongr with k hk s hs
        exact (sum_Aset_le ν i T k s).trans (opt_skip ν hsupp i k s)

/-- (B1): plays while the arm is still young. -/
lemma termB1 (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N)
    (L : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, tsLaw ν {ω | tsArm ω t = i ∧ (tsPlays ω t i : ℝ) < L} ≤
      (⌈L⌉₊ : ENNReal) := by
  have hm := mean_mem ν hsupp i
  calc _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range ⌈L⌉₊, ∑ s ∈ Finset.range (k + 1),
          tsLaw ν (Aset i t k s) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        have hsub : {ω | tsArm ω t = i ∧ (tsPlays ω t i : ℝ) < L} ⊆
            ⋃ k ∈ Finset.range ⌈L⌉₊, ⋃ s ∈ Finset.range (k + 1), Aset i t k s := by
          rintro ω ⟨ha, hL⟩
          simp only [Set.mem_iUnion, exists_prop, Finset.mem_range]
          refine ⟨tsPlays ω t i, Nat.lt_ceil.mpr hL, (tsCounts ω t).1 i, ?_, rfl, rfl, ha⟩
          rw [tsPlays_eq]; omega
        exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _))
    _ = ∑ k ∈ Finset.range ⌈L⌉₊, ∑ s ∈ Finset.range (k + 1),
          ∑ t ∈ Finset.range T, tsLaw ν (Aset i t k s) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ ≤ ∑ k ∈ Finset.range ⌈L⌉₊, ∑ s ∈ Finset.range (k + 1),
          ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν i) s) := by
        gcongr with k hk s hs
        exact (sum_Aset_le ν i T k s).trans (opt_skip ν hsupp i k s)
    _ = ∑ k ∈ Finset.range ⌈L⌉₊, (1 : ENNReal) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => pmf_nonneg' _ _ hm.1 hm.2 _), pmf_sum',
          ENNReal.ofReal_one]
    _ = _ := by simp

/-- (B2): old arm, low empirical mean, but a high posterior sample. -/
lemma termB2 (ν : StochasticBandit N) (i : Fin N) (x y L : ℝ) (T : ℕ) (ε : ENNReal)
    (hβ : ∀ a b : ℕ, L ≤ ((a + b : ℕ) : ℝ) → (a : ℝ) ≤ x * ((a + b : ℕ) : ℝ) →
      betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Ioi y) ≤ ε) :
    ∑ t ∈ Finset.range T, tsLaw ν {ω | L ≤ (tsPlays ω t i : ℝ) ∧
        ((tsCounts ω t).1 i : ℝ) ≤ x * (tsPlays ω t i : ℝ) ∧ y < tsTheta ω t i} ≤ T * ε := by
  calc _ ≤ ∑ t ∈ Finset.range T, ε := Finset.sum_le_sum (fun t _ => ?_)
    _ = T * ε := by simp
  set G := ((Finset.range (t + 1)) ×ˢ (Finset.range (t + 1))).filter
    (fun p : ℕ × ℕ => L ≤ ((p.1 + p.2 : ℕ) : ℝ) ∧ (p.1 : ℝ) ≤ x * ((p.1 + p.2 : ℕ) : ℝ)) with hG
  have hsub : {ω | L ≤ (tsPlays ω t i : ℝ) ∧
        ((tsCounts ω t).1 i : ℝ) ≤ x * (tsPlays ω t i : ℝ) ∧ y < tsTheta ω t i} ⊆
      ⋃ p ∈ G, {ω | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2 ∧ y < tsTheta ω t i} := by
    rintro ω ⟨h1, h2, h3⟩
    simp only [Set.mem_iUnion, exists_prop]
    have hle := tsPlays_le ω t i
    have heq := tsPlays_eq ω t i
    refine ⟨((tsCounts ω t).1 i, (tsCounts ω t).2 i), ?_, rfl, rfl, h3⟩
    rw [hG, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    rw [heq] at h1 h2
    refine ⟨⟨by omega, by omega⟩, h1, h2⟩
  have hdisj : Set.PairwiseDisjoint (↑G : Set (ℕ × ℕ))
      (fun p => {ω : TSOmega N | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2}) := by
    intro p _ p' _ hpp'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact hpp' (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2'))
  calc tsLaw ν _ ≤ ∑ p ∈ G, tsLaw ν {ω | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2 ∧
        y < tsTheta ω t i} := (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ p ∈ G, betaMeasure ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1) (Set.Ioi y) *
          tsLaw ν {ω | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2} :=
        Finset.sum_congr rfl (fun p _ => roundB ν i y t p.1 p.2)
    _ ≤ ∑ p ∈ G, ε * tsLaw ν {ω | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2} := by
        gcongr with p hp
        rw [hG, Finset.mem_filter] at hp
        exact hβ p.1 p.2 hp.2.1 hp.2.2
    _ = ε * tsLaw ν (⋃ p ∈ G, {ω | (tsCounts ω t).1 i = p.1 ∧ (tsCounts ω t).2 i = p.2}) := by
        rw [← Finset.mul_sum, measure_biUnion_finset hdisj
          (fun p _ => cset_meas t (fun c => c.1 i = p.1 ∧ c.2 i = p.2))]
    _ ≤ ε * 1 := by gcongr; exact prob_le_one
    _ = ε := mul_one _

/-- (C): plays with a low posterior sample, charged to the plays of arm `0`. -/
lemma termC (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N)
    (y : ℝ) (T : ℕ) (q : ℕ → ℕ → ℝ)
    (hq : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Ioi y) = ENNReal.ofReal (q k s))
    (hq' : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Iic y) = ENNReal.ofReal (1 - q k s))
    (hqpos : ∀ k s, 0 < q k s) :
    ∑ t ∈ Finset.range T, tsLaw ν {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y} ≤
      ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
        ENNReal.ofReal (min ((1 - q k s) / q k s) (T : ℝ) *
          AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν 0) s) := by
  have hm := mean_mem ν hsupp 0
  set S1 : ℕ → ℕ → ℕ → Set (TSOmega N) := fun t k s =>
    {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y ∧ (tsCounts ω t).1 0 = s ∧ (tsCounts ω t).2 0 = k - s}
    with hS1
  calc _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
          tsLaw ν (S1 t k s) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        have hsub : {ω | tsArm ω t = i ∧ tsTheta ω t i ≤ y} ⊆
            ⋃ k ∈ Finset.range T, ⋃ s ∈ Finset.range (k + 1), S1 t k s := by
          rintro ω ⟨ha, hy⟩
          simp only [Set.mem_iUnion, exists_prop, Finset.mem_range]
          have hle := tsPlays_le ω t 0
          have heq := tsPlays_eq ω t 0
          refine ⟨tsPlays ω t 0, lt_of_le_of_lt hle (Finset.mem_range.mp ht),
            (tsCounts ω t).1 0, by omega, ha, hy, rfl, by omega⟩
        exact (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _))
    _ = ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
          ∑ t ∈ Finset.range T, tsLaw ν (S1 t k s) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ ≤ _ := by
        gcongr with k hk s hs
        have hsk : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        set f := AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν 0) s with hf
        have hf0 : 0 ≤ f := pmf_nonneg' _ _ hm.1 hm.2 _
        have hQ := opt_skip ν hsupp 0 k s
        set X := ∑ t ∈ Finset.range T, tsLaw ν (S1 t k s) with hX
        -- (a) comparison with plays of arm 0
        have ha : ENNReal.ofReal (q k s) * X ≤ ENNReal.ofReal ((1 - q k s) * f) := by
          rw [hX, Finset.mul_sum]
          calc ∑ t ∈ Finset.range T, ENNReal.ofReal (q k s) * tsLaw ν (S1 t k s)
              ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (1 - q k s) * tsLaw ν (Aset 0 t k s) := by
                refine Finset.sum_le_sum (fun t _ => ?_)
                have hr := roundC ν i y t s (k - s)
                rw [hq k s hsk, hq' k s hsk] at hr
                refine hr.trans (mul_le_mul_of_nonneg_left (measure_mono ?_) (zero_le))
                rintro ω ⟨h0, h1, h2⟩
                refine ⟨?_, h1, h0⟩
                rw [tsPlays_eq, h1, h2]; omega
            _ = ENNReal.ofReal (1 - q k s) * ∑ t ∈ Finset.range T, tsLaw ν (Aset 0 t k s) := by
                rw [Finset.mul_sum]
            _ ≤ ENNReal.ofReal (1 - q k s) * ENNReal.ofReal f := by
                gcongr; exact (sum_Aset_le ν 0 T k s).trans hQ
            _ = ENNReal.ofReal ((1 - q k s) * f) := by
                by_cases h1q : 0 ≤ 1 - q k s
                · rw [ENNReal.ofReal_mul h1q]
                · push Not at h1q
                  rw [ENNReal.ofReal_of_nonpos h1q.le, zero_mul,
                    ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h1q.le hf0)]
        -- (b) the trivial bound
        have hb : X ≤ ENNReal.ofReal ((T : ℝ) * f) := by
          calc X ≤ ∑ t ∈ Finset.range T, tsLaw ν (Qset 0 k s) := by
                refine Finset.sum_le_sum (fun t _ => measure_mono ?_)
                rintro ω ⟨_, _, h1, h2⟩
                refine ⟨t, ?_, h1⟩
                rw [tsPlays_eq, h1, h2]; omega
            _ ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal f := Finset.sum_le_sum (fun t _ => hQ)
            _ = ENNReal.ofReal ((T : ℝ) * f) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul
                  (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
        have hqp := hqpos k s
        have ha' : X ≤ ENNReal.ofReal ((1 - q k s) / q k s * f) := by
          have hne : ENNReal.ofReal (q k s) ≠ 0 := by
            rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hqp
          have h2 : X * ENNReal.ofReal (q k s) ≤ ENNReal.ofReal ((1 - q k s) * f) := by
            rw [mul_comm]; exact ha
          have := (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr h2
          refine this.trans (le_of_eq ?_)
          rw [← ENNReal.ofReal_div_of_pos hqp]
          congr 1; ring
        rw [min_mul_of_nonneg _ _ hf0]
        rcases le_total ((1 - q k s) / q k s * f) ((T : ℝ) * f) with h | h
        · rw [min_eq_left h]; exact ha'
        · rw [min_eq_right h]; exact hb

/-- Per-arm bound on the expected number of plays. -/
theorem arm_bound (ν : StochasticBandit N) (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1) (i : Fin N)
    (x y L : ℝ) (T : ℕ) (ε : ENNReal)
    (hβ : ∀ a b : ℕ, L ≤ ((a + b : ℕ) : ℝ) → (a : ℝ) ≤ x * ((a + b : ℕ) : ℝ) →
      betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Ioi y) ≤ ε)
    (q : ℕ → ℕ → ℝ)
    (hq : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Ioi y) = ENNReal.ofReal (q k s))
    (hq' : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Iic y) = ENNReal.ofReal (1 - q k s))
    (hqpos : ∀ k s, 0 < q k s) :
    ∫⁻ ω, (tsPlays ω T i : ENNReal) ∂(tsLaw ν) ≤
      (∑ k ∈ Finset.range T, ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
        ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν i) s)) +
      (⌈L⌉₊ : ENNReal) + T * ε +
      ∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
        ENNReal.ofReal (min ((1 - q k s) / q k s) (T : ℝ) *
          AgrawalGoyalTS.TwoArmed.binomPMF k (banditArmMean ν 0) s) := by
  rw [plays_lintegral]
  refine le_trans ?_ (add_le_add (add_le_add (add_le_add (termA ν hsupp i x T)
    (termB1 ν hsupp i L T)) (termB2 ν i x y L T ε hβ)) (termC ν hsupp i y T q hq hq' hqpos))
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun t _ => ?_)
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
  intro ω (h : tsArm ω t = i)
  by_cases h1 : x * (tsPlays ω t i : ℝ) < ((tsCounts ω t).1 i : ℝ)
  · exact Or.inl (Or.inl (Or.inl ⟨h, h1⟩))
  by_cases h2 : (tsPlays ω t i : ℝ) < L
  · exact Or.inl (Or.inl (Or.inr ⟨h, h2⟩))
  by_cases h3 : y < tsTheta ω t i
  · exact Or.inl (Or.inr ⟨not_lt.mp h2, not_lt.mp h1, h3⟩)
  · exact Or.inr ⟨h, not_lt.mp h3⟩

end E20FW


namespace E20Main

open AgrawalGoyalTS.TwoArmed AgrawalGoyalTS.NArmed BanditAlgorithm

lemma cdf_le_one (n : ℕ) (p x : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : binomCDF n p x ≤ 1 := by
  rw [← E20Unif.pmf_sum n p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun s _ _ => E20Unif.pmf_nonneg n p hp0 hp1 s)

lemma cdf_nonneg (n : ℕ) (p x : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binomCDF n p x :=
  Finset.sum_nonneg (fun s _ => E20Unif.pmf_nonneg n p hp0 hp1 s)

lemma beta_Iic (a b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Iic y) =
      ENNReal.ofReal (1 - binomCDF (a + b + 1) y a) := by
  have h := fact1 (a + 1) (b + 1) (by omega) (by omega) y hy0 hy1
  have e : a + 1 + (b + 1) - 1 = a + b + 1 := by omega
  rw [e] at h
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  rw [← h]
  unfold betaCDF
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma beta_Ioi (a b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Ioi y) =
      ENNReal.ofReal (binomCDF (a + b + 1) y a) := by
  have hc := cdf_le_one (a + b + 1) y (a : ℝ) hy0 hy1
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, beta_Iic a b y hy0 hy1,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

lemma termA_real (T : ℕ) (hT : 2 ≤ T) (μ d L x : ℝ) (hx : x = μ + d) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hd : 0 < d) (hL0 : 0 ≤ L) (hL : Real.exp (-2 * L * d ^ 2) ≤ 1 / T) :
    ∑ k ∈ Finset.range T, ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
      binomPMF k μ s ≤ L + 2 := by
  subst hx
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hterm : ∀ k : ℕ, ∑ s ∈ (Finset.range (k + 1)).filter
      (fun s : ℕ => (μ + d) * (k : ℝ) < (s : ℝ)), binomPMF k μ s =
        1 - binomCDF k μ ((k : ℝ) * μ + (k : ℝ) * d) := by
    intro k
    rw [E20Hoeff.one_sub_cdf]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext s
    simp only [Finset.mem_filter, not_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  simp_rw [hterm]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun k : ℕ => (k : ℝ) < L),
    show L + 2 = (L + 1) + 1 by ring]
  refine add_le_add ?_ ?_
  · calc _ ≤ ∑ k ∈ (Finset.range T).filter (fun k : ℕ => (k : ℝ) < L), (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => by linarith [cdf_nonneg k μ ((k : ℝ) * μ + (k : ℝ) * d) hμ0 hμ1])
      _ = ((Finset.range T).filter (fun k : ℕ => (k : ℝ) < L)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (⌈L⌉₊ : ℝ) := by
          have hsub : (Finset.range T).filter (fun k : ℕ => (k : ℝ) < L) ⊆ Finset.range (⌈L⌉₊) := by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
            exact Nat.lt_ceil.mpr hk.2
          have := Finset.card_le_card hsub
          rw [Finset.card_range] at this
          exact_mod_cast this
      _ ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
  · calc _ ≤ ∑ k ∈ (Finset.range T).filter (fun k : ℕ => ¬ (k : ℝ) < L), 1 / (T : ℝ) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hkL : L ≤ (k : ℝ) := not_lt.mp (Finset.mem_filter.mp hk).2
          refine ((binom_hoeff k μ hμ0 hμ1 d hd.le).2.1).trans (le_trans ?_ hL)
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg d])
      _ = ((Finset.range T).filter (fun k : ℕ => ¬ (k : ℝ) < L)).card * (1 / (T : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T : ℝ) * (1 / T) := by
          gcongr
          have := Finset.card_filter_le (Finset.range T) (fun k : ℕ => ¬ (k : ℝ) < L)
          rw [Finset.card_range] at this
          exact_mod_cast this
      _ = 1 := by field_simp

theorem arm_main {N : ℕ} [NeZero N] (ν : StochasticBandit N)
    (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (i : Fin N) (hi : i ≠ 0)
    (T : ℕ) (hT : 2 ≤ T) :
    ENNReal.ofReal (gapTo0 ν i) * ∫⁻ ω, (tsPlays ω T i : ENNReal) ∂(tsLaw ν) ≤
      ENNReal.ofReal (1323 * Real.log T / gapTo0 ν i ^ 2) := by
  have hm0 := E20FW.mean_mem ν hsupp 0
  have hmi := E20FW.mean_mem ν hsupp i
  have hlt := hopt i hi
  set μ0 := banditArmMean ν 0 with hμ0
  set μi := banditArmMean ν i with hμi
  set D := gapTo0 ν i with hD
  have hDdef : D = μ0 - μi := rfl
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hD1 : D ≤ 1 := by rw [hDdef]; linarith [hm0.2, hmi.1]
  set d := D / 3 with hd
  have hdpos : 0 < d := by positivity
  have hd1 : d ≤ 1 := by linarith
  set x := μi + d with hx
  set y := μi + 2 * d with hy
  have hx0 : 0 ≤ x := by linarith [hmi.1]
  have hy0 : 0 ≤ y := by linarith [hmi.1]
  have hyμ : μ0 - y = d := by rw [hy, hd]; linarith [hDdef]
  have hxy : x = y - d := by rw [hx, hy]; ring
  have hy1 : y < 1 := by linarith [hm0.2]
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  set l := Real.log T with hl
  have hl2 : 1 / 2 ≤ l := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hT2
    linarith
  set L := l / (2 * d ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  have hLexp : Real.exp (-2 * L * d ^ 2) ≤ 1 / T := by
    have : -2 * L * d ^ 2 = -l := by rw [hL]; field_simp
    rw [this, Real.exp_neg, hl, Real.exp_log hTpos, one_div]
  have hβ : ∀ a b : ℕ, L ≤ ((a + b : ℕ) : ℝ) → (a : ℝ) ≤ x * ((a + b : ℕ) : ℝ) →
      betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1) (Set.Ioi y) ≤ ENNReal.ofReal (1 / T) := by
    intro a b hab hax
    rw [beta_Ioi a b y hy0 hy1.le]
    apply ENNReal.ofReal_le_ofReal
    have hn : ((a + b + 1 : ℕ) : ℝ) = ((a + b : ℕ) : ℝ) + 1 := by push_cast; ring
    have hthr : (a : ℝ) ≤ ((a + b + 1 : ℕ) : ℝ) * y - ((a + b + 1 : ℕ) : ℝ) * d := by
      rw [hn]; nlinarith
    refine (E20CSum.cdf_mono_x (a + b + 1) y hy0 hy1.le hthr).trans
      (((binom_hoeff (a + b + 1) y hy0 hy1.le d hdpos.le).1).trans (le_trans ?_ hLexp))
    exact Real.exp_le_exp.mpr (by rw [hn]; nlinarith [sq_nonneg d])
  have hq : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Ioi y) =
        ENNReal.ofReal (binomCDF (k + 1) y s) := by
    intro k s hsk
    rw [beta_Ioi s (k - s) y hy0 hy1.le, show s + (k - s) + 1 = k + 1 by omega]
  have hq' : ∀ k s : ℕ, s ≤ k →
      betaMeasure ((s : ℝ) + 1) (((k - s : ℕ) : ℝ) + 1) (Set.Iic y) =
        ENNReal.ofReal (1 - binomCDF (k + 1) y s) := by
    intro k s hsk
    rw [beta_Iic s (k - s) y hy0 hy1.le, show s + (k - s) + 1 = k + 1 by omega]
  have hab := E20FW.arm_bound ν hsupp i x y L T (ENNReal.ofReal (1 / T)) hβ
    (fun k s => binomCDF (k + 1) y s) hq hq' (fun k s => E20Unif.cdf_pos (k + 1) y hy0 hy1 s)
  -- the four terms
  have hA : (∑ k ∈ Finset.range T, ∑ s ∈ (Finset.range (k + 1)).filter
      (fun s : ℕ => x * (k : ℝ) < (s : ℝ)), ENNReal.ofReal (binomPMF k μi s)) ≤
        ENNReal.ofReal (L + 2) := by
    have e : ∀ k : ℕ, ∑ s ∈ (Finset.range (k + 1)).filter (fun s : ℕ => x * (k : ℝ) < (s : ℝ)),
        ENNReal.ofReal (binomPMF k μi s) = ENNReal.ofReal (∑ s ∈ (Finset.range (k + 1)).filter
          (fun s : ℕ => x * (k : ℝ) < (s : ℝ)), binomPMF k μi s) := fun k =>
      (ENNReal.ofReal_sum_of_nonneg (fun s _ => E20Unif.pmf_nonneg k μi hmi.1 hmi.2 s)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => Finset.sum_nonneg
      (fun s _ => E20Unif.pmf_nonneg k μi hmi.1 hmi.2 s))]
    exact ENNReal.ofReal_le_ofReal (termA_real T hT μi d L x hx hmi.1 hmi.2 hdpos hL0 hLexp)
  have hB1 : (⌈L⌉₊ : ENNReal) ≤ ENNReal.ofReal (L + 1) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one hL0).le
  have hB2 : (T : ENNReal) * ENNReal.ofReal (1 / T) ≤ ENNReal.ofReal 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by field_simp))
  have hC : (∑ k ∈ Finset.range T, ∑ s ∈ Finset.range (k + 1),
      ENNReal.ofReal (min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) *
        binomPMF k μ0 s)) ≤ ENNReal.ofReal (((4 * l + 4) / d ^ 2 + 1) / d + 2) := by
    have hnn : ∀ k s : ℕ, 0 ≤ min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) *
        binomPMF k μ0 s := by
      intro k s
      refine mul_nonneg (le_min (div_nonneg (by linarith [cdf_le_one (k + 1) y (s : ℝ) hy0 hy1.le])
        (cdf_nonneg (k + 1) y s hy0 hy1.le)) (Nat.cast_nonneg T))
        (E20Unif.pmf_nonneg k μ0 hm0.1 hm0.2 s)
    have e : ∀ k : ℕ, ∑ s ∈ Finset.range (k + 1),
        ENNReal.ofReal (min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) *
          binomPMF k μ0 s) = ENNReal.ofReal (∑ s ∈ Finset.range (k + 1),
            min ((1 - binomCDF (k + 1) y s) / binomCDF (k + 1) y s) (T : ℝ) * binomPMF k μ0 s) :=
      fun k => (ENNReal.ofReal_sum_of_nonneg (fun s _ => hnn k s)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => Finset.sum_nonneg (fun s _ => hnn k s))]
    exact ENNReal.ofReal_le_ofReal (E20CSum.csum T hT μ0 y d hdpos hd1 hy0 hyμ hm0.2)
  have hCnn : 0 ≤ ((4 * l + 4) / d ^ 2 + 1) / d + 2 := by
    have : 0 ≤ l := by linarith
    positivity
  have htot : ∫⁻ ω, (tsPlays ω T i : ENNReal) ∂(tsLaw ν) ≤
      ENNReal.ofReal ((L + 2) + (L + 1) + 1 + (((4 * l + 4) / d ^ 2 + 1) / d + 2)) := by
    refine hab.trans ?_
    rw [ENNReal.ofReal_add (by positivity) hCnn, ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
  have hreal : D * ((L + 2) + (L + 1) + 1 + (((4 * l + 4) / d ^ 2 + 1) / d + 2)) ≤
      1323 * l / D ^ 2 := by
    have key : D * ((L + 2) + (L + 1) + 1 + (((4 * l + 4) / d ^ 2 + 1) / d + 2)) =
        (9 * l * D + 6 * D ^ 3 + 108 * l + 108 + 3 * D ^ 2) / D ^ 2 := by
      rw [hL, hd]; field_simp; ring
    rw [key]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : l * D ≤ l := by nlinarith
    have h2 : D ^ 3 ≤ 1 := pow_le_one₀ hDpos.le hD1
    have h3 : D ^ 2 ≤ 1 := pow_le_one₀ hDpos.le hD1
    nlinarith
  calc ENNReal.ofReal D * ∫⁻ ω, (tsPlays ω T i : ENNReal) ∂(tsLaw ν)
      ≤ ENNReal.ofReal D * ENNReal.ofReal ((L + 2) + (L + 1) + 1 +
          (((4 * l + 4) / d ^ 2 + 1) / d + 2)) := by gcongr
    _ = ENNReal.ofReal (D * ((L + 2) + (L + 1) + 1 + (((4 * l + 4) / d ^ 2 + 1) / d + 2))) :=
        (ENNReal.ofReal_mul hDpos.le).symm
    _ ≤ ENNReal.ofReal (1323 * l / D ^ 2) := ENNReal.ofReal_le_ofReal hreal

theorem main (N : ℕ) [NeZero N] (hN : 2 ≤ N) (ν : StochasticBandit N)
    (hsupp : ∀ i, ν.P i (Set.Icc 0 1) = 1)
    (hopt : ∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) (T : ℕ) (hT : 2 ≤ T) :
    tsRegret ν T ≤ ENNReal.ofReal (1400 * (∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
      1 / gapTo0 ν a ^ 2) ^ 2 * Real.log T) := by
  rw [E20FW.regret_eq ν hopt T]
  set F := Finset.univ.filter (fun a : Fin N => a ≠ 0) with hF
  set S := ∑ a ∈ F, 1 / gapTo0 ν a ^ 2 with hS
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hgap : ∀ a ∈ F, 0 < gapTo0 ν a ∧ gapTo0 ν a ≤ 1 := by
    intro a ha
    have hne := (Finset.mem_filter.mp ha).2
    have h1 := hopt a hne
    have h2 := E20FW.mean_mem ν hsupp 0
    have h3 := E20FW.mean_mem ν hsupp a
    unfold gapTo0
    constructor <;> linarith [h2.2, h3.1]
  have hS1 : 1 ≤ S := by
    have h1 : (⟨1, by omega⟩ : Fin N) ∈ F := by
      rw [hF, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h => ?_⟩
      have := congrArg Fin.val h
      simp at this
    obtain ⟨hg0, hg1⟩ := hgap _ h1
    calc (1 : ℝ) ≤ 1 / gapTo0 ν ⟨1, by omega⟩ ^ 2 := by
          rw [le_div_iff₀ (by positivity), one_mul]
          exact pow_le_one₀ hg0.le hg1
      _ ≤ S := Finset.single_le_sum (f := fun a => 1 / gapTo0 ν a ^ 2) (fun a ha => by
            have := (hgap a ha).1
            positivity) h1
  calc ∑ a ∈ F, ENNReal.ofReal (gapTo0 ν a) * ∫⁻ ω, (tsPlays ω T a : ENNReal) ∂(tsLaw ν)
      ≤ ∑ a ∈ F, ENNReal.ofReal (1323 * Real.log T / gapTo0 ν a ^ 2) :=
        Finset.sum_le_sum (fun a ha => arm_main ν hsupp hopt a (Finset.mem_filter.mp ha).2 T hT)
    _ = ENNReal.ofReal (∑ a ∈ F, 1323 * Real.log T / gapTo0 ν a ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg (fun a _ =>
          div_nonneg (mul_nonneg (by norm_num) hl) (sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal (1400 * S ^ 2 * Real.log T) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∑ a ∈ F, 1323 * Real.log T / gapTo0 ν a ^ 2 = 1323 * Real.log T * S := by
          rw [hS, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        rw [e]
        have hS2 : S ≤ S ^ 2 := by nlinarith
        have h1 : 1323 * Real.log T * S ≤ 1323 * Real.log T * S ^ 2 :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
        nlinarith [sq_nonneg S]

end E20Main

open MeasureTheory BanditAlgorithm AgrawalGoyalTS.NArmed in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ ν : StochasticBandit N,
      (∀ i, ν.P i (Set.Icc 0 1) = 1) →
      (∀ i, i ≠ 0 → banditArmMean ν i < banditArmMean ν 0) → ∀ T : ℕ, 2 ≤ T →
        AgrawalGoyalTS.TwoArmed.tsRegret ν T ≤
          ENNReal.ofReal (C * (∑ a ∈ Finset.univ.filter (fun a : Fin N => a ≠ 0),
            1 / gapTo0 ν a ^ 2) ^ 2 * Real.log T) := by
  refine ⟨1400, by norm_num, ?_⟩
  intro N _ hN ν hsupp hopt T hT
  exact E20Main.main N hN ν hsupp hopt T hT
