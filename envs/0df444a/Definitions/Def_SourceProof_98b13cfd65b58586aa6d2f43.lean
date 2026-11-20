-- Prove2me | Definitions.Def_SourceProof_98b13cfd65b58586aa6d2f43
-- name    : SourceProof_98b13cfd65b58586aa6d2f43
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:13:23.802968+00:00
-- url     : https://prove2.me/theorems/abb2000f-66ad-4088-92a2-1e6a667b63f0
-- title:
--   LevyStochCalc source module: SourceProof_98b13cfd65b58586aa6d2f43
-- statement:
--   The original source theorem `ProbabilityTheory.measure_exists_abs_gt_le` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
import Definitions.Def_SourceProof_43f1d351fc8089295565fd5b

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

theorem _root_.Prove2MeSourceProof.h_98b13cfd65b58586aa6d2f43 [IsFiniteMeasure μ] {ε : ℝ}
    (hX : IsRealQuasimartingale 𝓕 X μ) (hε : 0 < ε) (hT : T.Countable) :
    μ {ω | ∃ s ∈ T ∩ Set.Iic t, ε < |X s ω|}
      ≤ ENNReal.ofReal (2 * (variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
          + ∫ ω, |X t ω| ∂μ) / ε) := by
  have : {ω | ∃ s ∈ T ∩ Set.Iic t, ε < |X s ω|} =
      ⋃ F ∈ {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}, {ω | ∃ s ∈ F, ε < |X s ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.subset_inter_iff, Set.mem_iUnion, exists_prop]
    refine ⟨fun ⟨s, hsT, hs⟩ ↦ ?_, fun ⟨F, hF, ⟨s, hsT, hs⟩⟩ ↦ ?_⟩
    · exact ⟨{s}, by grind, by grind⟩
    · exact ⟨s, by grind, by grind⟩
  rw [this]
  have hcnt : {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t}.Countable :=
    ProbabilityTheory.countable_setOf_finset_coe_subset (hT.mono Set.inter_subset_left)
  have hdir : DirectedOn (Function.onFun (· ⊆ ·) fun F : Finset ι ↦ {ω | ∃ s ∈ F, ε < |X s ω|})
      {F : Finset ι | ↑F ⊆ T ∩ Set.Iic t} :=
    fun F₁ h₁ F₂ h₂ ↦ ⟨F₁ ∪ F₂, by grind, by grind, by grind⟩
  rw [measure_biUnion_eq_iSup hcnt hdir]
  refine iSup₂_le fun F hF ↦ ?_
  have hF' : ∀ s ∈ F, s ≤ t := fun s hs ↦ (hF hs).2
  calc μ {ω | ∃ s ∈ F, ε < |X s ω|}
      = ENNReal.ofReal (μ.real {ω | ∃ s ∈ F, ε < |X s ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (_root_.Prove2MeSourceProof.h_43f1d351fc8089295565fd5b (μ := μ) hX.stronglyAdapted hX.integrable
          (hX.integral_indicator_le_variationBound t) hε hF')
end CountableEvents

end ProbabilityTheory


