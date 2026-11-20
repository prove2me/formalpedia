-- Prove2me | Definitions.Def_SourceProof_436b1ce988647b7e9b7772ec
-- name    : SourceProof_436b1ce988647b7e9b7772ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:01:55.671807+00:00
-- url     : https://prove2.me/theorems/7f8dad93-f9d2-43e5-ad23-bcc1b1c1ee75
-- title:
--   LevyStochCalc source module: SourceProof_436b1ce988647b7e9b7772ec
-- statement:
--   The original source theorem `ProbabilityTheory.ae_exists_bound''` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000
import Definitions.Def_SourceProof_98b13cfd65b58586aa6d2f43

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

theorem _root_.Prove2MeSourceProof.h_436b1ce988647b7e9b7772ec [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (t : ι) :
    ∀ᵐ ω ∂μ, ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic t, |X s' ω| ≤ M + 1 := by
  rw [ae_iff]
  push Not
  have : {a | ∀ (M : ℕ), ∃ s' ∈ T ∩ Set.Iic t, ↑M + 1 < |X s' a|}
      = ⋂ M : ℕ, {a | ∃ s' ∈ T ∩ Set.Iic t, (M + 1 : ℝ) < |X s' a|} := by ext; simp
  rw [this]
  refine le_antisymm ?_ zero_le
  have hbound (M : ℕ) :
      μ (⋂ M : ℕ, {ω | ∃ s ∈ T ∩ Set.Iic t, (M + 1 : ℝ) < |X s ω|})
        ≤ ENNReal.ofReal (2 * (ProbabilityTheory.variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
            + ∫ ω, |X t ω| ∂μ) / (M + 1)) := by
    refine (measure_mono (Set.iInter_subset _ M)).trans ?_
    exact _root_.Prove2MeSourceProof.h_98b13cfd65b58586aa6d2f43 hX (by positivity) hT
  have hlim : Tendsto (fun M : ℕ ↦
      ENNReal.ofReal (2 * (ProbabilityTheory.variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
        + ∫ ω, |X t ω| ∂μ) / (M + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have h1 : Tendsto (fun n : ℕ ↦ (2 * (ProbabilityTheory.variationBound X 𝓕 μ t +
        ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ)) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun M ↦ ?_
    simp
  exact ge_of_tendsto' hlim hbound
end CountableEvents

end ProbabilityTheory


