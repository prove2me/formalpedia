-- Prove2me | Definitions.Def_SourceProof_6dec83132bd9fad97f9eee54
-- name    : SourceProof_6dec83132bd9fad97f9eee54
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:00:33.03954+00:00
-- url     : https://prove2.me/theorems/0a86503b-978f-405f-8be5-62c7ac32d946
-- title:
--   LevyStochCalc source module: SourceProof_6dec83132bd9fad97f9eee54
-- statement:
--   The original source theorem `ProbabilityTheory.lintegral_sup_rpow_edist_le_of_minimal_cover_two` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

theorem _root_.Prove2MeSourceProof.h_6dec83132bd9fad97f9eee54 (hp : 1 ≤ p)
    (hX : IsAEKolmogorovProcess X P p q M) {ε₀ : ℝ≥0} (hε : ε₀ ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε₀ * 2⁻¹ ^ n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hdq : d < q)
    (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p := by
  refine (ProbabilityTheory.lintegral_sup_rpow_edist_le_of_minimal_cover hp hX ?_ hC hC_subset hC_card
    h_cov hm).trans ?_
  · intro n
    rw [← mul_one (Metric.ediam J), ENNReal.coe_mul]
    gcongr
    norm_cast
    apply pow_le_one₀ <;> norm_num
  rw [mul_comm _ c₁]
  conv_rhs => rw [mul_comm _ c₁]
  simp only [mul_assoc, mul_div_assoc]
  gcongr c₁ * ?_
  simp only [← mul_assoc]
  rw [mul_comm (2 ^ d), mul_assoc]
  gcongr M * ?_
  simp only [ENNReal.coe_mul, ENNReal.coe_pow]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat]
  calc (∑ j ∈ Finset.range (k - m),
          ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j + 1)) ^ (-d / p) * (ε₀ * 2⁻¹ ^ (m + j)) ^ (q / p)) ^ p
    _ = (∑ j ∈ Finset.range (k - m),
          ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j)) ^ (q / p + (-d / p)) * 2⁻¹ ^ (-d / p)) ^ p := ?_
    _ ≤ 2 ^ d * ((2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p) := ?_
  · congr with j
    rw [pow_add, ← mul_assoc, ENNReal.mul_rpow_of_ne_top
      (by apply ENNReal.mul_ne_top <;> simp) (by simp)]
    rw [mul_comm, ← mul_assoc,
      ← ENNReal.rpow_add_of_add_pos (by apply ENNReal.mul_ne_top <;> simp), pow_one]
    rw [← add_div]
    bound
  rw [← Finset.sum_mul, ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
  rw [mul_comm]
  gcongr
  · rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ (by bound), ← zpow_neg_one,
      ← ENNReal.rpow_intCast_mul]
    simp
  conv_rhs => rw [div_eq_mul_inv, ← ENNReal.rpow_neg]
  calc (∑ i ∈ Finset.range (k - m), ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + i)) ^ (q / p + -d / p)) ^ p
    _ = (∑ i ∈ Finset.range (k - m), ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m)) ^ ((q - d) / p) *
          (2⁻¹ ^ ((q - d) / p)) ^ i) ^ p := ?_
    _ ≤ (2 * ↑ε₀ * 2⁻¹ ^ m) ^ (q - d) * (2 ^ ((q - d) / p) - 1) ^ (-p) := ?_
  · congr with i
    rw [neg_div, ← sub_eq_add_neg, ← sub_div, pow_add, ← mul_assoc, ENNReal.mul_rpow_of_nonneg
      _ _ (div_nonneg (sub_nonneg_of_le (le_of_lt hdq)) (by bound))]
    congr 1
    rw [← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast, mul_comm]
  rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by bound), ← ENNReal.rpow_mul,
    div_mul_cancel₀ _ (by bound), mul_assoc 2, mul_comm 2, ENNReal.mul_rpow_of_nonneg _ 2
      (sub_nonneg_of_le (le_of_lt hdq)), mul_assoc]
  gcongr _ * ?_
  calc (∑ i ∈ Finset.range (k - m), ((2⁻¹ : ℝ≥0∞) ^ ((q - d) / p)) ^ i) ^ p
    _ ≤ (∑' (i : ℕ), ((2⁻¹ : ℝ≥0∞) ^ ((q - d) / p)) ^ i) ^ p :=
          by gcongr; apply ENNReal.sum_le_tsum
    _ = ((1 - (2⁻¹ ^ ((q - d) / p)))⁻¹) ^ p := by congr 1; apply ENNReal.tsum_geometric _
    _ ≤ 2 ^ (q - d) * (2 ^ ((q - d) / p) - 1) ^ (-p) := ?_
  rw [← neg_one_mul p, ENNReal.rpow_mul, ← ENNReal.rpow_inv_rpow (y := p) (by bound) (2 ^ (q - d))]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
  gcongr
  conv_rhs => rw [← ENNReal.rpow_mul, ← div_eq_mul_inv]; rw (occs := [1]) [← one_mul ((q - d) / p)]
  rw (occs := [1]) [← neg_neg (1 : ℝ), ← neg_one_mul, mul_assoc (-1), mul_comm (-1)]
  rw [ENNReal.rpow_mul, ← ENNReal.mul_rpow_of_ne_top (by norm_num) (by norm_num),
    AddLECancellable.mul_tsub (ENNReal.cancel_of_ne (by simp))]
  rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  simp only [neg_mul, one_mul, neg_add_cancel, ENNReal.rpow_zero, mul_one]
  rw [← zpow_neg_one, ← zpow_neg_one, ← ENNReal.rpow_intCast_mul]
  simp [← ENNReal.rpow_intCast]
end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

end Together

end ProbabilityTheory


