-- Prove2me | Definitions.Def_SourceProof_ade94c0fef305d69001e8022
-- name    : SourceProof_ade94c0fef305d69001e8022
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:38:04.291483+00:00
-- url     : https://prove2.me/theorems/5dba3dfa-b135-441a-85ea-dc01671d286d
-- title:
--   LevyStochCalc source module: SourceProof_ade94c0fef305d69001e8022
-- statement:
--   The original source theorem `ProbabilityTheory.finite_kolmogorov_chentsov` comes from the `BrownianMotion.Continuity.KolmogorovChentsovInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F001
import Definitions.Def_SourceProof_5f079cb9d9f49aa6f930a140
import Definitions.Def_SourceProof_adcacbe25f775ede4346d632
import Definitions.Def_SourceProof_cb622b835076370ac58f9fd2

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

theorem _root_.Prove2MeSourceProof.h_ade94c0fef305d69001e8022
    (hT : HasBoundedCoveringNumber U c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (T' : Set T) [hT' : Finite T'] (hT'U : T' ⊆ U) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β U := by
  have h_diam : Metric.ediam U < ∞ := hT.ediam_lt_top
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  simp only [ProbabilityTheory.constL, ← ENNReal.tsum_mul_left, ge_iff_le] at *
  by_cases h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : T'), edist (X s ω) (X t ω) = 0
  · convert zero_le
    rotate_left
    · infer_instance
    · infer_instance
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [h_ae] with ω h
    rw [Pi.zero_apply]
    rw [ENNReal.iSup_eq_zero]; rintro ⟨s, hs⟩
    rw [ENNReal.iSup_eq_zero]; rintro ⟨t, ht⟩
    simp [h ⟨s, hs⟩ ⟨t, ht⟩, hX.p_pos]
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    rw_mod_cast [h_ae] at hX
    exact hX.edist_eq_zero_of_const_eq_zero _ _
  have h_diam_zero : 0 < Metric.ediam U := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    apply hX.edist_eq_zero
    refine le_antisymm ?_ zero_le
    exact le_trans (Metric.edist_le_ediam_of_mem (hT'U s.2) (hT'U t.2)) h_ae
  have h_diam_real : 0 < (Metric.ediam U).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨h_diam_zero, h_diam⟩
  apply le_trans
    (_root_.Prove2MeSourceProof.h_adcacbe25f775ede4346d632 h_diam hX hβ_pos hT'U)
  apply ENNReal.tsum_le_tsum
  intro k
  wlog hc : c ≠ ∞
  · simp only [not_ne_iff.mp hc, ne_eq, ENNReal.rpow_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
      ENNReal.ofNat_ne_top, or_self, not_false_eq_true, ENNReal.mul_top, ENNReal.toReal_top,
      Real.logb_zero, zero_add]
    repeat rw [ENNReal.top_mul]
    · rw [ENNReal.mul_top hM]
      exact le_top
    · have : 0 < (k + 2) * d := by positivity
      simp [this]
    · simp [le_of_lt hdq_lt]
  have h_two : ENNReal.toNNReal 2 = 2 := rfl
  have h := _root_.Prove2MeSourceProof.h_cb622b835076370ac58f9fd2 (c := 2 ^ d * c) ?_ hT' hX ?_ hd_pos hdq_lt ?_
    (δ := (2 * 2⁻¹ ^ k * (Metric.ediam U + 1)).toNNReal)
  rotate_left
  · exact (_root_.Prove2MeSourceProof.h_5f079cb9d9f49aa6f930a140 hT) hT'U hd_pos.le
  · finiteness
  · simp [h_two, ENNReal.toNNReal_eq_zero_iff, h_diam.ne]
  rw [ENNReal.coe_toNNReal (by finiteness)] at h
  grw [h]
  rw [ENNReal.mul_rpow_of_ne_top (by finiteness) (by finiteness), ← mul_assoc,
    ← mul_assoc _ (2 ^ ((k : ℝ) * _)), ← mul_assoc (M : ℝ≥0∞)]
  refine mul_le_mul' (le_of_eq ?_) ?_
  · calc 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 * 2⁻¹ ^ k) ^ (q - d) * (Metric.ediam U + 1) ^ (q - d)))
    _ = 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 ^ (q - d) * 2 ^ (- k * (q - d)))
        * (Metric.ediam U + 1) ^ (q - d))) := by
      congr
      rw [ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by bound), ENNReal.rpow_neg,
        ← ENNReal.inv_pow, ENNReal.rpow_natCast]
    _ = M * (2 ^ (2 * p + 4 * q + 1) * (2 ^ (q - d) * 2 ^ d)) * c
        * (Metric.ediam U + 1) ^ (q - d)
        * (2 ^ (k * β * p) * 2 ^ (- k * (q - d))) := by ring
    _ = M * 2 ^ (2 * p + 5 * q + 1) * c * (Metric.ediam U + 1) ^ (q - d)
        * 2 ^ (↑k * (↑β * p - (q - d))) := by
      congr
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp), ← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
    _ = _ := by ring
  by_cases hc_zero : c.toReal = 0
  · simp only [ENNReal.toReal_mul, hc_zero, mul_zero, zero_mul, ENNReal.toNNReal_mul,
      ENNReal.toNNReal_pow, ENNReal.toNNReal_inv, inv_pow, NNReal.coe_mul, NNReal.coe_inv,
      NNReal.coe_pow, mul_inv_rev, inv_inv, Real.logb_zero, ENNReal.ofReal_zero, zero_add]
    gcongr
    exact zero_le
  gcongr with k
  simp only [ENNReal.toReal_mul, ENNReal.toNNReal_mul, h_two, ENNReal.toNNReal_pow,
    ENNReal.toNNReal_inv, inv_pow, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_inv, NNReal.coe_pow,
    mul_inv_rev, inv_inv, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
  calc Real.logb 2 (2^ d * c.toReal * 4 ^ d
      * (((Metric.ediam U + 1).toNNReal)⁻¹ * (2 ^ k * 2⁻¹)) ^ d)
  _ ≤ Real.logb 2 (2^ d * c.toReal * 4 ^ d * (2 ^ k * 2⁻¹) ^ d) := by
    gcongr 3
    · simp
    · refine mul_pos (by positivity) ?_
      refine Real.rpow_pos_of_pos ?_ _
      refine mul_pos ?_ (by positivity)
      simp [ENNReal.toNNReal_pos_iff, h_diam]
    · conv_rhs => rw [← one_mul (2 ^ k * 2⁻¹)]
      gcongr
      simp only [NNReal.coe_inv]
      rw [inv_le_one_iff₀]
      right
      simp only [NNReal.one_le_coe]
      rw [← ENNReal.toNNReal_one]
      gcongr
      · finiteness
      · exact CanonicallyOrderedAdd.le_add_self 1 (Metric.ediam U)
  _ = Real.logb 2 (c.toReal * (2^ d * 4 ^ d * (2 ^ k * 2⁻¹) ^ d)) := by ring_nf
  _ = Real.logb 2 (c.toReal * 2 ^ ((k + 2) * d)) := by
    congr
    rw [Real.mul_rpow (by simp) (by simp), Real.inv_rpow (by simp)]
    field_simp
    rw [add_mul, add_comm, Real.rpow_add (by simp), Real.rpow_mul (by simp),
      Real.rpow_mul (by simp)]
    norm_num
  _ ≤ Real.logb 2 c.toReal + (k + 2) * d := by
    rw [Real.logb_mul (by positivity) (by positivity)]
    gcongr
    rw [Real.logb_rpow (by simp) (by simp)]
end PseudoEMetricSpace

end ProbabilityTheory


