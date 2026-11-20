-- Prove2me | Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003
-- name    : BrownianMotion_Continuity_IsKolmogorovProcess_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:56:08.625175+00:00
-- url     : https://prove2.me/theorems/452e460f-67bc-4a89-a4af-e1a6d3f70843
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

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

lemma scale_change_lintegral_iSup
    {C : ℕ → Finset T}
    (hX : IsAEKolmogorovProcess X P p q M) (δ : ℝ≥0∞) (m k : ℕ) :
    ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ p * ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
          edist (X (chainingSequence C s k m) ω) (X (chainingSequence C t k m) ω) ^ p ∂P
        + 4 ^ p * ∫⁻ ω, ⨆ (s : C k), edist (X s ω) (X (chainingSequence C s k m) ω) ^ p ∂P := by
  rw [← lintegral_const_mul'', ← lintegral_const_mul'', ← lintegral_add_left']
  rotate_left
  · refine (AEMeasurable.iSup fun s ↦ AEMeasurable.iSup fun t ↦ ?_).const_mul _
    exact hX.aemeasurable_edist.pow_const _
  · exact AEMeasurable.iSup fun t ↦ hX.aemeasurable_edist.pow_const _
  · exact AEMeasurable.iSup fun s ↦ AEMeasurable.iSup fun t ↦ hX.aemeasurable_edist.pow_const _
  gcongr with ω
  exact scale_change_rpow m (fun s ↦ X s ω) _ _ hX.p_pos.le
end Together

end ProbabilityTheory


