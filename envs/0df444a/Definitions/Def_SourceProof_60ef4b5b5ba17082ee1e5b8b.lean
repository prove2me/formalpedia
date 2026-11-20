-- Prove2me | Definitions.Def_SourceProof_60ef4b5b5ba17082ee1e5b8b
-- name    : SourceProof_60ef4b5b5ba17082ee1e5b8b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:00:51.371359+00:00
-- url     : https://prove2.me/theorems/aaced7dc-6197-418a-af3b-7fc4d3d3367b
-- title:
--   LevyStochCalc source module: SourceProof_60ef4b5b5ba17082ee1e5b8b
-- statement:
--   The original source theorem `ProbabilityTheory.finite_set_bound_of_edist_le_of_le_diam` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F000
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003
import Definitions.Def_SourceProof_5f079cb9d9f49aa6f930a140
import Definitions.Def_SourceProof_70d2884df2ee11d00caa8bb9
import Definitions.Def_SourceProof_8dea9ce14ed47a706f6e5022

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

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_60ef4b5b5ba17082ee1e5b8b (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : δ / 4 ≤ Metric.ediam J) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * δ ^ (q - d)
        * (δ ^ d * (Nat.log2 (coveringNumber (δ / 4) J).toNat) ^ q
              * coveringNumber (δ / 4) J
            + c * Cp d p q) := by
  rcases isEmpty_or_nonempty J with hJ_empty | hJ_nonempty
  · simp
  replace hJ_nonempty : J.Nonempty := Set.nonempty_coe_sort.mp hJ_nonempty
  have hε' : Metric.ediam J < ∞ := hJ.ediam_lt_top
  let ε₀ := (Metric.ediam J).toNNReal
  rcases eq_zero_or_pos ε₀ with hε₀_eq_zero | hε₀_pos
  · simp only [ENNReal.toNNReal_eq_zero_iff, hε'.ne, or_false, ε₀] at hε₀_eq_zero
    suffices ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P = 0
      by simp [this]
    refine hX.lintegral_sup_rpow_edist_eq_zero' hJ_finite.countable ?_
    refine fun s t ↦ le_antisymm ?_ zero_le
    calc edist s t
    _ ≤ Metric.ediam J := Metric.edist_le_ediam_of_mem s.2 t.1.2
    _ = 0 := hε₀_eq_zero
  have hδ_le_mul : δ ≤ ε₀ * 4 := by
    rw [← ENNReal.coe_toNNReal hε'.ne, ENNReal.div_le_iff (by simp) (by simp)] at hδ_le
    norm_cast at hδ_le
  have hδ_div_pos : 0 < (δ / (ε₀ * 4)) := by
    positivity
  have h_logb_nonneg : 0 ≤ Real.logb 2⁻¹ (δ / (ε₀ * 4)).toReal := by
    refine Real.logb_nonneg_of_base_lt_one (by simp) (by field_simp; norm_num) hδ_div_pos ?_
    norm_cast
    field_simp
    exact hδ_le_mul
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (ε₀ : ℝ≥0∞) * 2⁻¹ ^ k <
      ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
    have := _root_.Prove2MeSourceProof.h_8dea9ce14ed47a706f6e5022 hε' hJ_finite hJ_nonempty
    convert this
    simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
  -- introduce covers
  have hε₀_mul_pos n : 0 < ε₀ * 2⁻¹ ^ n := by positivity
  let C' : ℕ → Set T := fun n ↦ minimalCover (ε₀ * 2⁻¹ ^ n) J
  have hC'_subset n : C' n ⊆ J := minimalCover_subset
  have hC'_fin n : (C' n).Finite := finite_minimalCover
  have hC'_card n : (C' n).encard = coveringNumber (ε₀ * 2⁻¹ ^ n) J :=
    encard_minimalCover (hJ_finite.totallyBounded.coveringNumber_ne_top (by positivity))
  have hC' n : IsCover (ε₀ * 2⁻¹ ^ n) J (C' n) :=
    isCover_minimalCover (hJ_finite.totallyBounded.coveringNumber_ne_top (by positivity))
  let C : ℕ → Finset T := fun n ↦ (hC'_fin n).toFinset
  have hC_subset n : (C n : Set T) ⊆ J := by simpa [C] using hC'_subset n
  have hC_card n : #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J := by
    rw [← hC'_card n]
    simp [C, ← Set.Finite.encard_eq_coe_toFinset_card]
  have hC n : IsCover (ε₀ * 2⁻¹ ^ n) J (C n) := by simpa [C] using hC' n
  -- change the supremum over `J` to a supremum over `C k`
  rw [← _root_.Prove2MeSourceProof.h_70d2884df2ee11d00caa8bb9 hX hJ_finite (hC k) (hC_subset k) (δ := δ)]
  swap; · simpa [ENNReal.inv_pow] using hk
  -- deal with the possibility that `δ < ε₀ * 2⁻¹ ^ k` (the l.h.s. is zero in this case)
  rcases lt_or_ge δ (ε₀ * 2⁻¹ ^ k) with hδ_lt | hδ_ge
  · suffices ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P = 0
      by simp [this]
    refine hX.lintegral_sup_rpow_edist_eq_zero' (J := C k) ?_ ?_
    · exact (hJ_finite.subset (hC_subset k)).countable
    intro s t
    by_contra! h_pos
    replace h_pos := h_pos.bot_lt
    rw [bot_eq_zero] at h_pos
    have hδ_lt_st : δ < edist s t := by
      have hδ_lt' : (δ : ℝ≥0∞) < ε₀ * 2⁻¹ ^ k := by
        have hδ_lt'' : (δ : ℝ≥0∞) <((ε₀ * 2⁻¹ ^ k : ℝ≥0) : ℝ≥0∞) := mod_cast hδ_lt
        simpa [ENNReal.inv_pow] using hδ_lt''
      refine (hδ_lt'.trans hk).trans_le ?_
      refine (iInf_le _ ⟨s, hC_subset k s.2⟩).trans ?_
      exact (iInf_le _ ⟨t.1, hC_subset k t.1.2⟩).trans (iInf_le _ h_pos)
    exact not_le.mpr hδ_lt_st t.2
  -- introduce `m` such that `ε₀ * 2⁻¹ ^ m ≤ δ ≤ ε₀ * 4 * 2⁻¹ ^ m` and `m ≤ k`
  let m := min k ⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊
  have hmk : m ≤ k := min_le_left _ _
  have hm' : m ≤ ⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊ := min_le_right _ _
  have hδ_eq_logb : δ = ε₀ * 4 * 2⁻¹ ^ (Real.logb 2⁻¹ (δ / (ε₀ * 4))) := by
    symm
    ext -- go to ℝ
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_inv]
    rw [mul_assoc, Real.rpow_logb (by simp) (by simp) (by positivity)]
    field
  have hmδ : ε₀ * 2⁻¹ ^ m ≤ δ := by
    unfold m
    rcases le_total k ⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊ with hk | hk
    · rwa [min_eq_left hk]
    · rw [min_eq_right hk]
      calc ε₀ * 2⁻¹ ^ ⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊
      _ = ε₀ * 4 * 2⁻¹ ^ ((⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊ : ℝ) + 2) := by
        rw [mul_assoc]
        congr
        rw [NNReal.rpow_add (by simp), mul_comm 4, mul_assoc]
        norm_num
      _ ≤ ε₀ * 4 * 2⁻¹ ^ (Real.logb 2⁻¹ (δ / (ε₀ * 4))) := by
        gcongr _ * ?_
        refine NNReal.rpow_le_rpow_of_exponent_ge (by simp) (by simp) ?_
        refine le_trans (Nat.le_ceil _) ?_
        norm_cast
        exact (Nat.ceil_le_floor_add_one _).trans (by simp)
      _ = δ := hδ_eq_logb.symm
  have hmδ₂ : δ ≤ ε₀ * 4 * 2⁻¹ ^ m := by
    calc δ
    _ = ε₀ * 4 * 2⁻¹ ^ (Real.logb 2⁻¹ (δ / (ε₀ * 4))) := hδ_eq_logb
    _ ≤ ε₀ * 4 * 2⁻¹ ^ (⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊ : ℝ) := by
      gcongr _ * ?_
      refine NNReal.rpow_le_rpow_of_exponent_ge (by simp) (by simp) ?_
      exact Nat.floor_le h_logb_nonneg
    _ = ε₀ * 4 * 2⁻¹ ^ ⌊Real.logb 2⁻¹ (δ / (ε₀ * 4))⌋₊ := by simp
    _ ≤ ε₀ * 4 * 2⁻¹ ^ m := by
      gcongr _ * ?_
      exact pow_le_pow_right_of_le_one' (by simp) (min_le_right _ _)
  -- change the scale: go to `C m`
  refine (ProbabilityTheory.scale_change_lintegral_iSup hX δ m k).trans ?_
  -- cut into two terms and apply previous lemmas
  simp_rw [mul_add]
  gcongr ?_ + ?_
  · have h_fst := ProbabilityTheory.lintegral_sup_rpow_edist_cover_rescale hX hJ_finite
        hC hC_subset hC_card (by positivity) hδ_le_mul hmδ hmδ₂ (m := m) (min_le_left _ _)
    grw [h_fst]
    have h_eq : (2 : ℝ≥0∞) ^ p * 2 ^ (p + 1) * M * 16 ^ q = 2 ^ (2 * p + 4 * q + 1) * M := by
      calc ((2 : ℝ≥0∞) ^ p * 2 ^ (p + 1)) * M * 16 ^ q
      _ = (2 ^ (2 * p) * 2) * M * 2 ^ (4 * q) := by
        rw [ENNReal.rpow_add _ _ (by simp) (by simp), ENNReal.rpow_one, ← mul_assoc,
          ← ENNReal.rpow_add _ _ (by simp) (by simp), ← two_mul,
          ENNReal.rpow_mul, ENNReal.rpow_mul]
        norm_cast
      _ = (2 ^ (2 * p) * 2 ^ (4 * q) * 2) * M := by ring
      _ = 2 ^ (2 * p + 4 * q + 1) * M := by
        rw [mul_comm _ (M : ℝ≥0∞), mul_assoc, mul_comm (M : ℝ≥0∞),
          ENNReal.rpow_add _ _ (by simp) (by simp), ENNReal.rpow_add _ _ (by simp) (by simp),
          ENNReal.rpow_one]
        simp_rw [← mul_assoc]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hX.q_pos.le, ENNReal.mul_rpow_of_nonneg _ _ hX.q_pos.le]
    simp_rw [← mul_assoc]
    rw [h_eq]
    refine le_of_eq ?_
    calc 2 ^ (2 * p + 4 * q + 1) * (M : ℝ≥0∞) * δ ^ q * (coveringNumber (δ / 4) J).toNat.log2 ^ q
        * coveringNumber (δ / 4) J
    _ = 2 ^ (2 * p + 4 * q + 1) * M * (δ ^ (q - d) * δ ^ d)
        * (coveringNumber (δ / 4) J).toNat.log2 ^ q * coveringNumber (δ / 4) J := by
      rw [← ENNReal.rpow_add _ _ (mod_cast hδ) (by simp)]
      ring_nf
    _ = _ := by ring
  · -- massage it a bit and apply `second_term_bound`
    simp_rw [add_assoc]
    rw [ENNReal.rpow_add _ _ (by positivity) (by simp)]
    simp_rw [mul_assoc]
    rw [ENNReal.rpow_mul]
    norm_num
    gcongr _ * ?_
    simp_rw [← mul_assoc]
    refine (ProbabilityTheory.second_term_bound hX ?_ hC hC_subset hC_card hdq_lt hJ hmk).trans ?_
    · simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
    change 2 ^ d * ↑M * c * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) * ProbabilityTheory.Cp d p q
      ≤ 2 ^ (4 * q + 1) * ↑M * δ ^ (q - d) * c * ProbabilityTheory.Cp d p q
    -- now use `ε₀ * 2⁻¹ ^ m ≤ δ` to get the result
    rw [mul_assoc _ (ε₀ : ℝ≥0∞)]
    have hmδ' : (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m ≤ δ := by
      have hmδ'' : ((ε₀ * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞) ≤ δ := mod_cast hmδ
      simpa [ENNReal.inv_pow] using hmδ''
    grw [hmδ']
    swap; · positivity
    gcongr ?_ * _
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
    calc 2 ^ d * M * c * (2 ^ (q - d) * δ ^ (q - d))
    _ = 2 ^ d * 2 ^ (q - d) * M * δ ^ (q - d) * c := by ring
    _ = 2 ^ q * M * δ ^ (q - d) * c := by
      rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
      ring_nf
    _ ≤ 2 ^ (4 * q + 1) * M * δ ^ (q - d) * c := by
      gcongr
      · norm_cast
      linarith
end Together

end ProbabilityTheory


