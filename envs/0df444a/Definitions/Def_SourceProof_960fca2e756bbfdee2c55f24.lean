-- Prove2me | Definitions.Def_SourceProof_960fca2e756bbfdee2c55f24
-- name    : SourceProof_960fca2e756bbfdee2c55f24
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:18:03.013447+00:00
-- url     : https://prove2.me/theorems/b9460987-d1f8-44aa-b72e-6b6c102367b5
-- title:
--   LevyStochCalc source module: SourceProof_960fca2e756bbfdee2c55f24
-- statement:
--   The original source theorem `ProbabilityTheory.lintegral_sup_rpow_edist_le_of_minimal_cover_two_of_le_one` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F001

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

theorem _root_.Prove2MeSourceProof.h_960fca2e756bbfdee2c55f24 (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M) {ε₀ : ℝ≥0} (hε : ε₀ ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε₀ * 2⁻¹ ^ n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hdq : d < q)
    (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ (q - d) - 1) := by
  have h_diam_lt_top : Metric.ediam J < ∞ := h_cov.ediam_lt_top
  have hε' : ε₀ ≠ ∞ := (hε.trans_lt h_diam_lt_top).ne
  refine (ProbabilityTheory.lintegral_sup_rpow_edist_le_of_minimal_cover_of_le_one hp hX ?_ hC hC_subset
    hC_card h_cov hm).trans ?_
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
  calc ∑ j ∈ Finset.range (k - m),
      ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j + 1)) ^ (-d) * ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j)) ^ q
    _ = ∑ j ∈ Finset.range (k - m), ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + j)) ^ (q - d) * 2⁻¹ ^ (-d) := by
      congr with j
      rw [pow_add, ← mul_assoc, ENNReal.mul_rpow_of_ne_top
        (by apply ENNReal.mul_ne_top <;> simp [hε']) (by simp)]
      rw [mul_comm, ← mul_assoc,
        ← ENNReal.rpow_add_of_add_pos (by apply ENNReal.mul_ne_top <;> simp [hε']),
        pow_one, ← sub_eq_add_neg]
      bound
    _ ≤ 2 ^ d * ((2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) / (2 ^ (q - d) - 1)) := ?_
  rw [← Finset.sum_mul, ENNReal.mul_rpow_of_nonneg _ _ (by bound), mul_comm]
  gcongr
  · rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
  calc ∑ i ∈ Finset.range (k - m), ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m + i)) ^ (q + -d)
    _ = ∑ i ∈ Finset.range (k - m), ((ε₀ : ℝ≥0∞) * 2⁻¹ ^ (m)) ^ (q - d) * (2⁻¹ ^ (q - d)) ^ i := by
      congr with i
      rw [← sub_eq_add_neg, pow_add, ← mul_assoc, ENNReal.mul_rpow_of_nonneg
        _ _ (sub_nonneg_of_le (le_of_lt hdq))]
      congr 1
      rw [← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast, mul_comm]
    _ ≤ (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) * (2 ^ (q - d) - 1)⁻¹ := ?_
    _ = (2 * ε₀) ^ (q - d) * (2⁻¹ ^ m) ^ (q - d) / (2 ^ (q - d) - 1) := by
      rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg_of_le hdq.le)]
  rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by bound), mul_comm (2 : ℝ≥0∞),
    mul_assoc _ (2 : ℝ≥0∞), mul_comm (2 : ℝ≥0∞),
    ENNReal.mul_rpow_of_nonneg _ _ (by bound), ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
  simp_rw [mul_assoc]
  gcongr _ * (_ * ?_)
  calc ∑ i ∈ Finset.range (k - m), ((2⁻¹ : ℝ≥0∞) ^ (q - d)) ^ i
    _ ≤ ∑' (i : ℕ), ((2⁻¹ : ℝ≥0∞) ^ (q - d)) ^ i := ENNReal.sum_le_tsum _
    _ = (1 - (2⁻¹ ^ (q - d)))⁻¹ := ENNReal.tsum_geometric _
    _ = (2⁻¹ ^ (q - d) * 2 ^ (q - d) - 2⁻¹ ^ (q - d))⁻¹ := by
      congr
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by bound), ENNReal.inv_mul_cancel]
        <;> simp
    _ = (2⁻¹ ^ (q - d) * (2 ^ (q - d) - 1))⁻¹ := by simp [ENNReal.mul_sub]
    _ = 2 ^ (q - d) * (2 ^ (q - d) - 1)⁻¹ := by
      rw [ENNReal.mul_inv (.inr (by finiteness)) (.inl (by simp)), ENNReal.inv_rpow, inv_inv]
end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

end Together

end ProbabilityTheory


