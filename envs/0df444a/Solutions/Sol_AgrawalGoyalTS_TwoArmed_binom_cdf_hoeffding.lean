-- Prove2me | solution 1 for AgrawalGoyalTS.TwoArmed.binom_cdf_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T16:28:19.919645+00:00
-- url     : https://prove2.me/submissions/a43d3f0c-e690-4d4b-a0cb-79c16cb512e4

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

open MeasureTheory
open AgrawalGoyalTS.TwoArmed

namespace Prove2BinomialSubmission



/- Source part: AcceptedBinomial.lean -/
namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace BayesProphet.MultiSec

noncomputable def binomialWeight (t : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (t.choose k : ℝ) * p ^ k * (1 - p) ^ (t - k)

lemma weight_nonneg (t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialWeight t p k := by
  unfold binomialWeight
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma weight_sum_one (t : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (t + 1), binomialWeight t p k = 1 := by
  have h := add_pow p (1 - p) t
  have hp : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp, one_pow] at h
  calc
    ∑ k ∈ Finset.range (t + 1), binomialWeight t p k
      = ∑ k ∈ Finset.range (t + 1), p ^ k * (1 - p) ^ (t - k) * (t.choose k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold binomialWeight
        ring
    _ = 1 := h.symm

lemma exp_dev (s p : ℝ) (t k : ℕ) :
    Real.exp (s * ((k : ℝ) - t * p)) =
      Real.exp (-(s * t * p)) * (Real.exp s) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma centred_mgf_factor (t : ℕ) (p s : ℝ) :
    (∑ k ∈ Finset.range (t + 1),
      binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
    ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t := by
  have hsum : (∑ k ∈ Finset.range (t + 1),
      binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
    (∑ k ∈ Finset.range (t + 1),
      (t.choose k : ℝ) * (p * Real.exp s) ^ k * (1 - p) ^ (t - k)) *
        Real.exp (-(s * t * p)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [exp_dev]
    unfold binomialWeight
    ring
  rw [hsum]
  have hbin : (p * Real.exp s + (1 - p)) ^ t =
      ∑ k ∈ Finset.range (t + 1),
        (t.choose k : ℝ) * (p * Real.exp s) ^ k * (1 - p) ^ (t - k) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← hbin]
  have hexp : Real.exp (-(s * t * p)) = (Real.exp (-(s * p))) ^ t := by
    rw [show -(s * t * p) = (t : ℝ) * (-(s * p)) by ring, Real.exp_nat_mul]
  rw [hexp, ← mul_pow]
  congr 1
  rw [add_mul]
  rw [mul_assoc]
  rw [← Real.exp_add]
  have harg : s + -(s * p) = s * (1 - p) := by ring
  rw [harg]
  ring

lemma bernoulli_mgf_le (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) ≤ Real.exp (s ^ 2 / 8) := by
  let q : unitInterval := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure (true : Bool) false q
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hmean : ∫ x, X x ∂μ = p := by
    simp [μ, X, q, ProbabilityTheory.integral_bernoulliMeasure]
  have hsub : HasSubgaussianMGF (fun b => X b - ∫ x, X x ∂μ) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    apply ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    · fun_prop
    · filter_upwards with x
      cases x <;> simp [X]
  have hle := hsub.mgf_le s
  have hmgf : mgf (fun b => X b - ∫ x, X x ∂μ) μ s =
      (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) := by
    rw [mgf, hmean, ProbabilityTheory.integral_bernoulliMeasure]
    simp only [X, q, Bool.false_eq_true, ↓reduceIte]
    ring_nf
  rw [hmgf] at hle
  norm_num at hle
  have hExp : (1 / 4 * s ^ 2 / 2) = s ^ 2 / 8 := by ring
  rw [hExp] at hle
  simpa [neg_mul] using hle

lemma factor_nonneg (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p)) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  exact add_nonneg (mul_nonneg hq (Real.exp_nonneg _)) (mul_nonneg hp0 (Real.exp_nonneg _))

lemma exp_tail_factor (s p ε : ℝ) (t k : ℕ) (w : ℝ) :
    Real.exp (-(s * (t : ℝ) * ε)) * (w * Real.exp (s * ((k : ℝ) - t * p))) =
      w * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
  calc
    Real.exp (-(s * (t : ℝ) * ε)) * (w * Real.exp (s * ((k : ℝ) - t * p)))
        = w * (Real.exp (-(s * (t : ℝ) * ε)) *
            Real.exp (s * ((k : ℝ) - t * p))) := by ring
    _ = w * Real.exp (-(s * (t : ℝ) * ε) + s * ((k : ℝ) - t * p)) := by
      rw [← Real.exp_add]
    _ = w * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
      congr 2
      ring

lemma upper_tail_le_exp (t : ℕ) {p ε s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    (∑ k ∈ (Finset.range (t + 1)).filter
        (fun k : ℕ => t * ε ≤ (k : ℝ) - t * p), binomialWeight t p k) ≤
      Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
  let F := (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * p)
  have h1 : (∑ k ∈ F, binomialWeight t p k) ≤
      ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hevent : t * ε ≤ (k : ℝ) - t * p := (Finset.mem_filter.mp hk).2
    have harg : 0 ≤ s * ((k : ℝ) - t * p - (t : ℝ) * ε) := by
      apply mul_nonneg hs
      linarith
    calc
      binomialWeight t p k = binomialWeight t p k * 1 := by ring
      _ ≤ binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp harg) (weight_nonneg t hp0 hp1 k)
  have h2 : (∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p - (t : ℝ) * ε))) =
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (exp_tail_factor s p ε t k (binomialWeight t p k)).symm
  have h3 : Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) ≤
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro k hk hkF
        exact mul_nonneg (weight_nonneg t hp0 hp1 k) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have h4 : (∑ k ∈ Finset.range (t + 1),
        binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p))) =
      ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t :=
    centred_mgf_factor t p s
  have h5 : ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t ≤
      Real.exp ((t : ℝ) * s ^ 2 / 8) := by
    have hpow := pow_le_pow_left₀ (factor_nonneg p s hp0 hp1)
      (bernoulli_mgf_le p s hp0 hp1) t
    calc
      ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t
          ≤ (Real.exp (s ^ 2 / 8)) ^ t := hpow
      _ = Real.exp ((t : ℝ) * s ^ 2 / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (∑ k ∈ F, binomialWeight t p k) ≤
        Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ F, binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := h1.trans h2.le
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * ((k : ℝ) - t * p)) := h3
    _ = Real.exp (-(s * (t : ℝ) * ε)) *
          ((1 - p) * Real.exp (-(s * p)) + p * Real.exp (s * (1 - p))) ^ t := by
      rw [h4]
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) * Real.exp ((t : ℝ) * s ^ 2 / 8) := by
      apply mul_le_mul_of_nonneg_left h5
      exact Real.exp_nonneg _
    _ = Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
      rw [← Real.exp_add]

lemma lower_tail_le_exp (t : ℕ) {p ε s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    (∑ k ∈ (Finset.range (t + 1)).filter
        (fun k : ℕ => (k : ℝ) - t * p ≤ -(t * ε)), binomialWeight t p k) ≤
      Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
  let F := (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * p ≤ -(t * ε))
  have h1 : (∑ k ∈ F, binomialWeight t p k) ≤
      ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hevent : (k : ℝ) - t * p ≤ -(t * ε) := (Finset.mem_filter.mp hk).2
    have harg : 0 ≤ s * (t * p - (k : ℝ) - (t : ℝ) * ε) := by
      apply mul_nonneg hs
      linarith
    calc
      binomialWeight t p k = binomialWeight t p k * 1 := by ring
      _ ≤ binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp harg) (weight_nonneg t hp0 hp1 k)
  have h2 : (∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε))) =
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ) - (t : ℝ) * ε))
          = binomialWeight t p k * (Real.exp (-(s * (t : ℝ) * ε)) *
              Real.exp (s * (t * p - (k : ℝ)))) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(s * (t : ℝ) * ε)) *
            (binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) := by ring
  have h3 : Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) ≤
      Real.exp (-(s * (t : ℝ) * ε)) *
        ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro k hk hkF
        exact mul_nonneg (weight_nonneg t hp0 hp1 k) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have hfull : (∑ k ∈ Finset.range (t + 1),
        binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) =
      ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
    calc
      (∑ k ∈ Finset.range (t + 1),
          binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ)))) =
          ∑ k ∈ Finset.range (t + 1),
            binomialWeight t p k * Real.exp ((-s) * ((k : ℝ) - t * p)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        ring
      _ = ((1 - p) * Real.exp (-((-s) * p)) + p * Real.exp ((-s) * (1 - p))) ^ t :=
        centred_mgf_factor t p (-s)
      _ = ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
        congr 1
        ring_nf
  have h5 : ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t ≤
      Real.exp ((t : ℝ) * s ^ 2 / 8) := by
    have hpow := pow_le_pow_left₀ (factor_nonneg p (-s) hp0 hp1)
      (bernoulli_mgf_le p (-s) hp0 hp1) t
    calc
      ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t
          = ((1 - p) * Real.exp (-((-s) * p)) + p * Real.exp ((-s) * (1 - p))) ^ t := by
        congr 1
        ring_nf
      _ ≤ (Real.exp ((-s) ^ 2 / 8)) ^ t := hpow
      _ = Real.exp ((t : ℝ) * s ^ 2 / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (∑ k ∈ F, binomialWeight t p k) ≤
        Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ F, binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := h1.trans h2.le
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) *
          ∑ k ∈ Finset.range (t + 1), binomialWeight t p k * Real.exp (s * (t * p - (k : ℝ))) := h3
    _ = Real.exp (-(s * (t : ℝ) * ε)) *
          ((1 - p) * Real.exp (s * p) + p * Real.exp (-(s * (1 - p)))) ^ t := by
      rw [hfull]
    _ ≤ Real.exp (-(s * (t : ℝ) * ε)) * Real.exp ((t : ℝ) * s ^ 2 / 8) := by
      apply mul_le_mul_of_nonneg_left h5
      exact Real.exp_nonneg _
    _ = Real.exp (-(s * (t : ℝ) * ε) + (t : ℝ) * s ^ 2 / 8) := by
      rw [← Real.exp_add]

theorem binomial_chernoff_hoeffding (t : ℕ) (α ε : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hε : 0 ≤ ε) :
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => (k : ℝ) - t * α ≤ -(t * ε)),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) ∧
    ∑ k ∈ (Finset.range (t + 1)).filter (fun k : ℕ => t * ε ≤ (k : ℝ) - t * α),
        (t.choose k : ℝ) * α ^ k * (1 - α) ^ (t - k) ≤ Real.exp (-2 * ε ^ 2 * t) := by
  have hs : 0 ≤ 4 * ε := by positivity
  constructor
  · have h := lower_tail_le_exp (t := t) (p := α) (ε := ε) (s := 4 * ε) hα₀ hα₁ hs
    have harg : -((4 * ε) * (t : ℝ) * ε) + (t : ℝ) * (4 * ε) ^ 2 / 8 =
        -2 * ε ^ 2 * (t : ℝ) := by ring
    simpa [binomialWeight, harg] using h
  · have h := upper_tail_le_exp (t := t) (p := α) (ε := ε) (s := 4 * ε) hα₀ hα₁ hs
    have harg : -((4 * ε) * (t : ℝ) * ε) + (t : ℝ) * (4 * ε) ^ 2 / 8 =
        -2 * ε ^ 2 * (t : ℝ) := by ring
    simpa [binomialWeight, harg] using h

end BayesProphet.MultiSec

end Prove2SwarmSubmission

/- Source part: Exponent.lean -/
namespace NativeBinomialCDF

/-- In the trivial-probability branch, the requested exponential upper bound is at least one. -/
theorem small_deviation_exponent_nonneg {N p δ : ℝ}
    (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (hdev : N * δ ≤ p) :
    0 ≤ 4 * δ - 2 * N * δ ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right (hdev.trans hp1) hδ
  nlinarith

/-- The effective deviation for the n+1-trial Chernoff bound is nonnegative in the other branch. -/
theorem shifted_deviation_nonneg {N p δ : ℝ}
    (hN : 0 ≤ N) (hdev : p ≤ N * δ) :
    0 ≤ (N * δ - p) / (N + 1) :=
  div_nonneg (sub_nonneg.mpr hdev) (by linarith)

/-- Centering the n+1-trial tail yields exactly the threshold displacement N*delta-p. -/
theorem shifted_deviation_mul {N p δ : ℝ} (hN : 0 ≤ N) :
    (N + 1) * ((N * δ - p) / (N + 1)) = N * δ - p := by
  have hden : N + 1 ≠ 0 := ne_of_gt (by linarith : 0 < N + 1)
  field_simp [hden]

/-- The nonempty-support cutoff supplies the exponent comparison without any delta upper bound. -/
theorem shifted_hoeffding_exponent_le {N p δ : ℝ}
    (hN : 0 ≤ N) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (hcut : N * p + N * δ ≤ N + 1) :
    -2 * ((N * δ - p) / (N + 1)) ^ 2 * (N + 1) ≤
      4 * δ - 2 * N * δ ^ 2 := by
  have hd : 0 < N + 1 := by linarith
  have hden : N + 1 ≠ 0 := ne_of_gt hd
  have hgap : 0 ≤ N + 1 - N * p - N * δ := by linarith
  have hlast : 0 ≤ N + 1 - N * p := by
    nlinarith [mul_le_mul_of_nonneg_left hp1 hN]
  have hidentity :
      (N * δ - p) ^ 2 - (N + 1) * (N * δ ^ 2 - 2 * δ) =
        p ^ 2 + δ * (N + 1 - N * p - N * δ) + δ * (N + 1 - N * p) := by
    ring
  have hpoly : 0 ≤
      (N * δ - p) ^ 2 - (N + 1) * (N * δ ^ 2 - 2 * δ) := by
    rw [hidentity]
    exact add_nonneg (add_nonneg (sq_nonneg p) (mul_nonneg hδ hgap))
      (mul_nonneg hδ hlast)
  have hexp :
      -2 * ((N * δ - p) / (N + 1)) ^ 2 * (N + 1) =
        (-2 * (N * δ - p) ^ 2) / (N + 1) := by
    field_simp [hden]
  rw [hexp]
  apply (div_le_iff₀ hd).2
  nlinarith [hpoly]

/-- Conversion to the literal ratio in the frozen target. -/
theorem target_exp_eq_ratio (N δ : ℝ) :
    Real.exp (4 * δ - 2 * N * δ ^ 2) =
      Real.exp (4 * δ) / Real.exp (2 * N * δ ^ 2) :=
  Real.exp_sub _ _

theorem one_le_target_ratio_of_small_deviation {N p δ : ℝ}
    (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (hdev : N * δ ≤ p) :
    1 ≤ Real.exp (4 * δ) / Real.exp (2 * N * δ ^ 2) := by
  rw [← target_exp_eq_ratio]
  exact Real.one_le_exp (small_deviation_exponent_nonneg hp1 hδ hdev)

theorem shifted_hoeffding_exp_le_ratio {N p δ : ℝ}
    (hN : 0 ≤ N) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (hcut : N * p + N * δ ≤ N + 1) :
    Real.exp (-2 * ((N * δ - p) / (N + 1)) ^ 2 * (N + 1)) ≤
      Real.exp (4 * δ) / Real.exp (2 * N * δ ^ 2) := by
  rw [← target_exp_eq_ratio]
  exact Real.exp_le_exp.mpr (shifted_hoeffding_exponent_le hN hp1 hδ hcut)

/-- Above the top support value, the strict upper-tail event is empty, including equality. -/
theorem no_strict_tail_above_support {N p δ k : ℝ}
    (hcut : N + 1 ≤ N * p + N * δ) (hk : k ≤ N + 1) :
    ¬ N * p + N * δ < k :=
  not_lt_of_ge (hk.trans hcut)

end NativeBinomialCDF

/- Source part: SumSupport.lean -/
namespace NativeBinomialCDF

open Prove2SwarmSubmission.BayesProphet.MultiSec

theorem succ_tail_le_one (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) :
    (∑ k ∈ (Finset.range (n + 2)).filter
      (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
      binomialWeight (n + 1) p k) ≤ 1 := by
  calc
    (∑ k ∈ (Finset.range (n + 2)).filter
        (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
        binomialWeight (n + 1) p k) ≤
        ∑ k ∈ Finset.range (n + 2), binomialWeight (n + 1) p k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro k _hk _hknot
        exact weight_nonneg (n + 1) hp0 hp1 k
    _ = 1 := weight_sum_one (n + 1) p

theorem succ_tail_eq_zero_of_cutoff (n : ℕ) (p δ : ℝ)
    (hcutoff : (n : ℝ) + 1 ≤ (n : ℝ) * p + (n : ℝ) * δ) :
    (∑ k ∈ (Finset.range (n + 2)).filter
      (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
      binomialWeight (n + 1) p k) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hkrange : k < n + 2 := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hknat : k ≤ n + 1 := by omega
  have hkreal : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hknat
  have hevent : (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ) :=
    (Finset.mem_filter.mp hk).2
  exact False.elim ((not_lt_of_ge (hkreal.trans hcutoff)) hevent)

end NativeBinomialCDF

/- Source part: SuccTail.lean -/
namespace NativeBinomialCDF

open Prove2SwarmSubmission.BayesProphet.MultiSec

theorem succ_upper_tail_weight (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ k ∈ (Finset.range (n + 2)).filter
      (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
      binomialWeight (n + 1) p k) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hcutoff : (n : ℝ) + 1 ≤ (n : ℝ) * p + (n : ℝ) * δ
  · rw [succ_tail_eq_zero_of_cutoff n p δ hcutoff]
    positivity
  · have hcut : (n : ℝ) * p + (n : ℝ) * δ ≤ (n : ℝ) + 1 :=
      (lt_of_not_ge hcutoff).le
    by_cases hdev : p ≤ (n : ℝ) * δ
    · let ε : ℝ := ((n : ℝ) * δ - p) / ((n : ℝ) + 1)
      have hε : 0 ≤ ε := shifted_deviation_nonneg hN0 hdev
      have heq : ((n + 1 : ℕ) : ℝ) * ε = (n : ℝ) * δ - p := by
        simpa only [ε, Nat.cast_add, Nat.cast_one] using
          (shifted_deviation_mul (N := (n : ℝ)) (p := p) (δ := δ) hN0)
      have hsubset :
          (Finset.range (n + 2)).filter
              (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)) ⊆
            (Finset.range ((n + 1) + 1)).filter
              (fun k : ℕ => ((n + 1 : ℕ) : ℝ) * ε ≤
                (k : ℝ) - ((n + 1 : ℕ) : ℝ) * p) := by
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hkrange, hktail⟩
        refine Finset.mem_filter.mpr ⟨hkrange, ?_⟩
        rw [heq]
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hktail]
      have hsums :
          (∑ k ∈ (Finset.range (n + 2)).filter
              (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
              binomialWeight (n + 1) p k) ≤
            ∑ k ∈ (Finset.range ((n + 1) + 1)).filter
              (fun k : ℕ => ((n + 1 : ℕ) : ℝ) * ε ≤
                (k : ℝ) - ((n + 1 : ℕ) : ℝ) * p),
              binomialWeight (n + 1) p k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro k _hk _hknot
        exact weight_nonneg (n + 1) hp0 hp1 k
      have hhoeffding :
          (∑ k ∈ (Finset.range ((n + 1) + 1)).filter
              (fun k : ℕ => ((n + 1 : ℕ) : ℝ) * ε ≤
                (k : ℝ) - ((n + 1 : ℕ) : ℝ) * p),
              binomialWeight (n + 1) p k) ≤
            Real.exp (-2 * ε ^ 2 * ((n + 1 : ℕ) : ℝ)) := by
        simpa only [binomialWeight] using
          (binomial_chernoff_hoeffding (n + 1) p ε hp0 hp1 hε).2
      have hbound : Real.exp (-2 * ε ^ 2 * ((n + 1 : ℕ) : ℝ)) ≤
          Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
        simpa only [ε, Nat.cast_add, Nat.cast_one] using
          (shifted_hoeffding_exp_le_ratio hN0 hp1 hδ hcut)
      exact hsums.trans (hhoeffding.trans hbound)
    · exact (succ_tail_le_one n p hp0 hp1 δ).trans
        (one_le_target_ratio_of_small_deviation hp1 hδ (lt_of_not_ge hdev).le)

theorem succ_upper_tail_explicit (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ k ∈ (Finset.range (n + 2)).filter
      (fun k : ℕ => (n : ℝ) * p + (n : ℝ) * δ < (k : ℝ)),
      ((n + 1).choose k : ℝ) * p ^ k * (1 - p) ^ ((n + 1) - k)) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  simpa only [binomialWeight] using succ_upper_tail_weight n p hp0 hp1 δ hδ

end NativeBinomialCDF



/-!
# Threshold conversions and the complement identity (verification-planner, %70)

Piece of `AgrawalGoyalTS.TwoArmed.binom_cdf_hoeffding` (theorem c69ab45e). Mathlib only.

The frozen `binomCDF n p x` is, by definition (module sha256 cd897a7a…),
`∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x), binomPMF n p k`, with
`binomPMF n p k = (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)`. So every sum below is
`binomCDF` after `unfold`, or by `rfl`. The hypotheses `hlow` and `hup` have exactly the shape
of the two conjuncts of the accepted `BayesProphet.MultiSec.binomial_chernoff_hoeffding`
(source 7fd9998e) at `t = n`, `α = p`, `ε = δ`.
-/

namespace BinomCDFThresholds

/-- The binomial masses sum to one (binomial theorem). -/
theorem sum_mass_eq_one (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = (1 : ℝ) by ring, one_pow] at h
  calc
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        = ∑ k ∈ Finset.range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 1 := h.symm

/-- Each binomial mass is nonnegative for `p ∈ [0, 1]`. -/
theorem mass_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- Complement identity: one minus the cdf at `x` is the strict upper tail at `x`. -/
theorem one_sub_lower_eq_upper (n : ℕ) (p x : ℝ) :
    1 - ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => x < (k : ℝ)),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun k : ℕ => (k : ℝ) ≤ x) (fun k : ℕ => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
  rw [sum_mass_eq_one n p] at hsplit
  have hnot : (Finset.range (n + 1)).filter (fun k : ℕ => x < (k : ℝ)) =
      (Finset.range (n + 1)).filter (fun k : ℕ => ¬ (k : ℝ) ≤ x) :=
    Finset.filter_congr (fun _ _ => not_le.symm)
  rw [hnot]
  exact sub_eq_iff_eq_add.mpr (hsplit.symm.trans (add_comm _ _))

/-- The strict upper tail of an `m`-trial binomial at `x` is at most the Hoeffding-shaped tail
`{k | T ≤ k - m * p}`, whenever `x < k` forces `T ≤ k - m * p`. -/
theorem upper_tail_le_of_imp (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x T : ℝ)
    (himp : ∀ k : ℕ, x < (k : ℝ) → T ≤ (k : ℝ) - m * p) :
    ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => x < (k : ℝ)),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) ≤
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => T ≤ (k : ℝ) - m * p),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.monotone_filter_right _ (fun k _ hk => himp k hk))
    (fun k _ _ => mass_nonneg m hp0 hp1 k)

/-- Threshold conversion for the lower tail: `k ≤ np - nδ ↔ k - np ≤ -(nδ)`. -/
theorem lower_filter_eq (n : ℕ) (p δ : ℝ) :
    (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p - (n : ℝ) * δ) =
      (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) - n * p ≤ -(n * δ)) :=
  Finset.filter_congr (fun _ _ => ⟨fun h => by linarith, fun h => by linarith⟩)

/-- (10), lower tail, in explicit-sum form, from the Hoeffding lower tail. -/
theorem lower_cdf_le (n : ℕ) (p δ : ℝ)
    (hlow : ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) - n * p ≤ -(n * δ)),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ Real.exp (-2 * δ ^ 2 * n)) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p - (n : ℝ) * δ),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) := by
  rw [lower_filter_eq n p δ]
  have he : -2 * (n : ℝ) * δ ^ 2 = -2 * δ ^ 2 * n := by ring
  rw [he]
  exact hlow

/-- (10), upper tail, in explicit-sum form: `1 - F(np + nδ)` is at most the Hoeffding upper
tail. -/
theorem one_sub_upper_cdf_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ)
    (hup : ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => n * δ ≤ (k : ℝ) - n * p),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ Real.exp (-2 * δ ^ 2 * n)) :
    1 - ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p + (n : ℝ) * δ),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) := by
  rw [one_sub_lower_eq_upper n p]
  have hsub := upper_tail_le_of_imp n hp0 hp1 ((n : ℝ) * p + (n : ℝ) * δ) ((n : ℝ) * δ)
    (fun _ hk => by linarith)
  have he : -2 * (n : ℝ) * δ ^ 2 = -2 * δ ^ 2 * n := by ring
  rw [he]
  exact hsub.trans hup

/-- The `(n + 1)`-trial complement in explicit-sum form: one minus the cdf at `np + nδ` is the
strict upper tail, at most the Hoeffding-shaped tail at any `T` with
`np + nδ < k → T ≤ k - (n + 1) p`; e.g. `T = nδ - p`. -/
theorem one_sub_succ_cdf_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) :
    1 - ∑ k ∈ (Finset.range (n + 1 + 1)).filter
          (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p + (n : ℝ) * δ),
        ((n + 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n + 1 - k) ≤
      ∑ k ∈ (Finset.range (n + 1 + 1)).filter
          (fun k : ℕ => (n : ℝ) * δ - p ≤ (k : ℝ) - ((n + 1 : ℕ) : ℝ) * p),
        ((n + 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n + 1 - k) := by
  rw [one_sub_lower_eq_upper (n + 1) p]
  refine upper_tail_le_of_imp (n + 1) hp0 hp1 _ _ (fun _ hk => ?_)
  rw [Nat.cast_add_one n]
  linarith

/-- The cdf is nonnegative, so one minus it is at most one. -/
theorem one_sub_cdf_le_one (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    1 - ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) ≤ 1 := by
  have h : 0 ≤ ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
      (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) :=
    Finset.sum_nonneg (fun k _ => mass_nonneg m hp0 hp1 k)
  linarith

/-- At or above the last atom the strict upper tail is empty: if `m ≤ x` then
`1 - F_m(x) = 0`. -/
theorem one_sub_cdf_eq_zero_of_le (m : ℕ) (p x : ℝ) (hx : (m : ℝ) ≤ x) :
    1 - ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) = 0 := by
  rw [one_sub_lower_eq_upper m p x]
  apply Finset.sum_eq_zero
  intro k hk
  exfalso
  rcases Finset.mem_filter.mp hk with ⟨hkr, hxk⟩
  have hkm : (k : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkr)
  linarith

end BinomCDFThresholds

namespace NativeBinomialCDF

/-- All three requested inequalities on explicit binomial prefix sums.
The pinned helper bodies supply its context in ExplicitBounds.lean. -/
theorem explicit_sum_cdf_hoeffding (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ k ∈ (Finset.range (n + 1)).filter
        (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p - (n : ℝ) * δ),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ≤
      Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - (∑ k ∈ (Finset.range (n + 1)).filter
        (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p + (n : ℝ) * δ),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ≤
      Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - (∑ k ∈ (Finset.range ((n + 1) + 1)).filter
        (fun k : ℕ => (k : ℝ) ≤ (n : ℝ) * p + (n : ℝ) * δ),
        ((n + 1).choose k : ℝ) * p ^ k * (1 - p) ^ ((n + 1) - k)) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  have hBayes := Prove2SwarmSubmission.BayesProphet.MultiSec.binomial_chernoff_hoeffding
    n p δ hp0 hp1 hδ
  refine ⟨BinomCDFThresholds.lower_cdf_le n p δ hBayes.1,
    BinomCDFThresholds.one_sub_upper_cdf_le n hp0 hp1 δ hBayes.2, ?_⟩
  exact
    (BinomCDFThresholds.one_sub_lower_eq_upper (n + 1) p
      ((n : ℝ) * p + (n : ℝ) * δ)).trans_le
        (succ_upper_tail_explicit n p hp0 hp1 δ hδ)

end NativeBinomialCDF


namespace AgrawalGoyalTS.TwoArmed

/-- Lemma 6 (p. 13), (10) and (11): for every natural `n`, `p ∈ [0,1]` and `δ ≥ 0`,
`F^B_{n,p}(np - nδ) ≤ e^{-2nδ²}`, `1 - F^B_{n,p}(np + nδ) ≤ e^{-2nδ²}` and
`1 - F^B_{n+1,p}(np + nδ) ≤ e^{4δ} / e^{2nδ²}`. -/
theorem binom_cdf_hoeffding (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    binomCDF n p ((n : ℝ) * p - (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF n p ((n : ℝ) * p + (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF (n + 1) p ((n : ℝ) * p + (n : ℝ) * δ) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  simpa only [binomCDF, binomPMF] using
    NativeBinomialCDF.explicit_sum_cdf_hoeffding n p hp0 hp1 δ hδ

end AgrawalGoyalTS.TwoArmed

end Prove2BinomialSubmission

theorem solution (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    binomCDF n p ((n : ℝ) * p - (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF n p ((n : ℝ) * p + (n : ℝ) * δ) ≤ Real.exp (-2 * (n : ℝ) * δ ^ 2) ∧
    1 - binomCDF (n + 1) p ((n : ℝ) * p + (n : ℝ) * δ) ≤
      Real.exp (4 * δ) / Real.exp (2 * (n : ℝ) * δ ^ 2) := by
  exact _root_.Prove2BinomialSubmission.AgrawalGoyalTS.TwoArmed.binom_cdf_hoeffding n p hp0 hp1 δ hδ
