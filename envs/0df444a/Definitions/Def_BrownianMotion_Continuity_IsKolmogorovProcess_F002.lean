-- Prove2me | Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
-- name    : BrownianMotion_Continuity_IsKolmogorovProcess_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:18:45.433864+00:00
-- url     : https://prove2.me/theorems/bd7176f9-ee06-41a0-90cc-5ad7abb3e96e
-- title:
--   Source declarations: BrownianMotion.Continuity.IsKolmogorovProcess
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.IsKolmogorovProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_FiniteInf_F000
import Definitions.Def_BrownianMotion_Auxiliary_MeanInequalities_F000
import Definitions.Def_BrownianMotion_Continuity_Chaining_F001
import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
import Definitions.Def_SourceProof_6dec83132bd9fad97f9eee54
import Definitions.Def_SourceProof_960fca2e756bbfdee2c55f24
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.EMetricSpace.PairReduction

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

noncomputable
def Cp (d p q : ℝ) : ℝ≥0∞ :=
  max (1 / ((2 ^ ((q - d) / p)) - 1) ^ p) (1 / (2 ^ (q - d) - 1))
lemma second_term_bound {C : ℕ → Finset T} {k m : ℕ}
    (hX : IsAEKolmogorovProcess X P p q M) {ε₀ : ℝ≥0} (hε : ε₀ ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε₀ * 2⁻¹ ^ n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hdq : d < q)
    (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * ε₀ * 2⁻¹ ^ m) ^ (q - d) * Cp d p q := by
  have h_diam_lt_top : Metric.ediam J < ∞ := h_cov.ediam_lt_top
  rw [Cp, mul_max, mul_one_div, mul_one_div]
  rcases le_total p 1 with hX.p_pos | hX.p_pos
  · exact (_root_.Prove2MeSourceProof.h_960fca2e756bbfdee2c55f24 hX.p_pos hX hε
      hC hC_subset hC_card hdq h_cov hm).trans (le_max_right _ _)
  · exact (_root_.Prove2MeSourceProof.h_6dec83132bd9fad97f9eee54 hX.p_pos hX hε
      hC hC_subset hC_card hdq h_cov hm).trans (le_max_left _ _)
end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

end Together

end ProbabilityTheory


