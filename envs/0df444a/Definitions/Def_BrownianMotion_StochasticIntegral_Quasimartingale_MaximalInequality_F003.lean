-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F003
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:03:45.732094+00:00
-- url     : https://prove2.me/theorems/9fa00e3c-0521-4847-8ff9-aad2f0311af2
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000
import Definitions.Def_SourceProof_436b1ce988647b7e9b7772ec

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

lemma ae_exists_bound [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) {T' : Set ι} (hT' : T'.Countable) :
    ∀ᵐ ω ∂μ, ∀ d ∈ T', ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic d, |X s' ω| ≤ M + 1 := by
  rw [ae_ball_iff hT']
  intro d hdT
  exact _root_.Prove2MeSourceProof.h_436b1ce988647b7e9b7772ec hX hT d
lemma ae_exists_bound' [IsFiniteMeasure μ] [(atTop : Filter ι).IsCountablyGenerated]
    (hX : IsRealQuasimartingale 𝓕 X μ) (hT : T.Countable) :
    ∀ᵐ ω ∂μ, ∀ d, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic d, |X s ω| ≤ M + 1 := by
  obtain ⟨u, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  suffices ∀ᵐ ω ∂μ, ∀ n, ∃ M : ℕ, ∀ s ∈ T ∩ Set.Iic (u n), |X s ω| ≤ M + 1 by
    filter_upwards [this] with ω hω d
    obtain ⟨n, hn⟩ : ∃ n, d ≤ u n := (hu.2.eventually_ge_atTop d).exists
    obtain ⟨M, hM⟩ := hω n
    exact ⟨M, fun s hsT ↦ hM s (by grind)⟩
  rw [ae_all_iff]
  exact fun n ↦ _root_.Prove2MeSourceProof.h_436b1ce988647b7e9b7772ec hX hT (u n)
end CountableEvents

end ProbabilityTheory


