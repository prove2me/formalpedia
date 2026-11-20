-- Prove2me | Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F001
-- name    : BrownianMotion_Continuity_IsKolmogorovProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:53:39.04702+00:00
-- url     : https://prove2.me/theorems/3dfca4e9-2eec-4fec-88d9-a77e9413ca45
-- title:
--   Source declarations: BrownianMotion.Continuity.IsKolmogorovProcess
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.IsKolmogorovProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

lemma lintegral_sup_rpow_edist_le_sum_rpow_of_le_one (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ ∑ i ∈ Finset.range (k - m), ∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence C t k (m + i)) ω)
          (X (chainingSequence C t k (m + i + 1)) ω) ^ p ∂P := by
  rw [← lintegral_finsetSum' _ (fun _ _ => .iSup (fun _ => hX.aemeasurable_edist.pow_const _))]
  gcongr with ω
  refine le_trans ?_ (Finset.iSup_sum_le _)
  gcongr with t
  refine le_trans ?_ (ENNReal.rpow_finsetSum_le_finsetSum_rpow hX.p_pos hp)
  gcongr
  · exact hX.p_pos.le
  · exact edist_chainingSequence_le_sum_edist (X · ω) hm
lemma lintegral_sup_rpow_edist_le_sum_of_le_one (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (ε n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ M * ∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) * (ε (m + i) : ℝ≥0∞) ^ q := by
  refine (lintegral_sup_rpow_edist_le_sum_rpow_of_le_one hp hX hm).trans ?_
  rw [Finset.mul_sum]
  gcongr with i hi
  refine (lintegral_sup_rpow_edist_succ hX hC hC_subset ?_).trans_eq (by ring)
  simp only [Finset.mem_range] at hi
  omega
lemma lintegral_sup_rpow_edist_le_of_minimal_cover_of_le_one (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hε : ∀ n, ε n ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ M * c₁
        * ∑ j ∈ Finset.range (k - m), ε (m + j + 1) ^ (- d) * (ε (m + j) : ℝ≥0∞) ^ q := by
  refine (lintegral_sup_rpow_edist_le_sum_of_le_one hp hX hC hC_subset hm).trans ?_
  simp_rw [Finset.mul_sum, mul_assoc]
  gcongr ∑ i ∈ _, _ * ?_ with i hi
  rw [← mul_assoc]
  gcongr
  refine le_trans (le_of_eq ?_) ((h_cov.coveringNumber_le (ε (m + i + 1)) (hε _)).trans_eq ?_)
  · norm_cast
    exact hC_card _
  · rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

end Together

end ProbabilityTheory


