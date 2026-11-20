-- Prove2me | Definitions.Def_SourceProof_076e0ed6a50324520d425fcf
-- name    : SourceProof_076e0ed6a50324520d425fcf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:00:17.619298+00:00
-- url     : https://prove2.me/theorems/c3f0edb7-eb87-4450-8f45-32ffd1567235
-- title:
--   LevyStochCalc source module: SourceProof_076e0ed6a50324520d425fcf
-- statement:
--   The original source theorem `ProbabilityTheory.finite_set_bound_of_edist_le_of_diam_le` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F000
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003
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

theorem _root_.Prove2MeSourceProof.h_076e0ed6a50324520d425fcf (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hδ_le : Metric.ediam J ≤ δ / 4) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ p * 2 ^ q * M * c * δ ^ (q - d) * Cp d p q := by
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
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (ε₀ : ℝ≥0∞) * 2⁻¹ ^ k <
      ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
    have := _root_.Prove2MeSourceProof.h_8dea9ce14ed47a706f6e5022 hε' hJ_finite hJ_nonempty
    convert this
    simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
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
  have hX.q_pos_pos : 0 < q := hd_pos.trans hdq_lt
  rw [← _root_.Prove2MeSourceProof.h_70d2884df2ee11d00caa8bb9 hX hJ_finite (hC k) (hC_subset k) (δ := δ)]
  swap; · simpa [ENNReal.inv_pow] using hk
  -- change the scale: go to `C 0`.
  refine (ProbabilityTheory.scale_change_lintegral_iSup hX δ 0 k).trans ?_
  -- the first term of the sum is zero because `C 0` is a singleton
  have hC_zero : #(C 0) ≤ 1 := by
    suffices (#(C 0) : ℕ∞) = 1 by norm_cast at this; simp [this]
    simp only [hC_card 0, pow_zero, mul_one, ε₀]
    exact coveringNumber_eq_one_of_ediam_le hJ_nonempty (by rw [ENNReal.coe_toNNReal hε'.ne])
  have h_first_eq_zero :
      ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
          edist (X (chainingSequence C s k 0) ω) (X (chainingSequence C t k 0) ω) ^ p ∂P
        = 0 := by
    refine (lintegral_eq_zero_iff' ?_).mpr (ae_of_all _ fun ω ↦ ?_)
    · refine AEMeasurable.iSup fun s ↦ AEMeasurable.iSup fun t ↦ ?_
      exact hX.aemeasurable_edist.pow_const _
    simp only [Pi.zero_apply, ENNReal.iSup_eq_zero, ENNReal.rpow_eq_zero_iff]
    intro s t
    suffices chainingSequence C s k 0 = chainingSequence C t k 0 by simp [this, hX.p_pos]
    rw [Finset.card_le_one_iff] at hC_zero
    exact hC_zero (chainingSequence_mem hC hJ_nonempty s.2 0 zero_le)
      (chainingSequence_mem hC hJ_nonempty t.1.2 0 zero_le)
  simp only [h_first_eq_zero, mul_zero, zero_add]
  -- the second term is bounded by the result we want
  simp_rw [mul_assoc]
  gcongr
  simp_rw [← mul_assoc]
  refine (ProbabilityTheory.second_term_bound hX ?_ hC hC_subset hC_card hdq_lt hJ zero_le).trans ?_
  · simp [ε₀, ENNReal.coe_toNNReal hε'.ne]
  simp only [pow_zero, mul_one]
  have hδ_le' : Metric.ediam J ≤ δ := by
    refine hδ_le.trans ?_
    rw [ENNReal.div_le_iff (by simp) (by simp)]
    conv_lhs => rw [← mul_one δ, ENNReal.coe_mul]
    gcongr
    norm_cast
  simp only [ε₀, ENNReal.coe_toNNReal hε'.ne]
  grw [hδ_le']
  swap; · positivity
  refine le_of_eq ?_
  calc 2 ^ d * M * c * (2 * δ) ^ (q - d) * ProbabilityTheory.Cp d p q
  _ = 2 ^ d * 2 ^ (q - d) * M * c * δ ^ (q - d) * ProbabilityTheory.Cp d p q := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by bound)]
    ring
  _ = 2 ^ q * M * c * δ ^ (q - d) * ProbabilityTheory.Cp d p q := by
    rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
    ring_nf
end Together

end ProbabilityTheory


