-- Prove2me | Definitions.Def_SourceProof_8dea9ce14ed47a706f6e5022
-- name    : SourceProof_8dea9ce14ed47a706f6e5022
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:59:28.345047+00:00
-- url     : https://prove2.me/theorems/a93429da-bd9f-4b49-8ace-88e9add99dcd
-- title:
--   LevyStochCalc source module: SourceProof_8dea9ce14ed47a706f6e5022
-- statement:
--   The original source theorem `ProbabilityTheory.exists_nat_pow_lt_iInf` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
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

open Filter in
open scoped Topology in
theorem _root_.Prove2MeSourceProof.h_8dea9ce14ed47a706f6e5022 (hJ : Metric.ediam J < ∞) (hJ_finite : J.Finite)
    (hJ_nonempty : J.Nonempty) :
    ∃ k : ℕ, Metric.ediam J * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
  let ε₀ := Metric.ediam J
  suffices 0 < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t by
    suffices ∀ᶠ k in atTop,
        ε₀ * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t from this.exists
    have h_tendsto : Tendsto (fun n ↦ ε₀ * 2⁻¹ ^ n) atTop (𝓝 0) := by
      rw [← mul_zero (ε₀ : ℝ≥0∞)]
      change Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ ↦ p.1 * p.2) ∘ (fun n : ℕ ↦ (ε₀, 2⁻¹ ^ n))) atTop
        (𝓝 (ε₀ * 0))
      refine (ENNReal.tendsto_mul (a := ε₀) (b := 0) (by simp) (.inr hJ.ne)).comp ?_
      refine Tendsto.prodMk_nhds tendsto_const_nhds ?_
      exact ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr (by simp)
    exact h_tendsto.eventually_lt_const this
  -- `⊢ 0 < ⨅ s, ⨅ t, ⨅ (_ : 0 < edist s t), edist s t`, since `J` is nonempty and finite
  rw [iInf_subtype]
  change 0 < ⨅ s ∈ J, ⨅ (t : J) (_h : 0 < edist s t), edist s t
  rw [hJ_finite.lt_iInf_iff hJ_nonempty]
  intro s hsJ
  rw [iInf_subtype]
  change 0 < ⨅ t ∈ J, ⨅ (_h : 0 < edist s t), edist s t
  rw [hJ_finite.lt_iInf_iff hJ_nonempty]
  intro t htJ
  by_cases hst : 0 < edist s t <;> simp [hst]
end Together

end ProbabilityTheory


