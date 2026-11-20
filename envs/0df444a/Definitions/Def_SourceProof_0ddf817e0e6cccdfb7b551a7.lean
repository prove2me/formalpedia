-- Prove2me | Definitions.Def_SourceProof_0ddf817e0e6cccdfb7b551a7
-- name    : SourceProof_0ddf817e0e6cccdfb7b551a7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:44:20.28103+00:00
-- url     : https://prove2.me/theorems/890dfba6-15c0-4083-b700-653baae51cf7
-- title:
--   LevyStochCalc source module: SourceProof_0ddf817e0e6cccdfb7b551a7
-- statement:
--   The original source theorem `ProbabilityTheory.measurable_rightLimWithin` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000
import Definitions.Def_SourceProof_cba8008674f3dd8a34a01708

/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/

/-! # Cadlag modification of quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section CountableEvents

variable [OrderBot ι] {T : Set ι} {t : ι}

end CountableEvents

section RegularitySet

variable [OrderBot ι]

variable [TopologicalSpace ι] [OrderTopology ι]

end RegularitySet

variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

end Accumulation

open Function

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
theorem _root_.Prove2MeSourceProof.h_0ddf817e0e6cccdfb7b551a7 [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    Measurable (fun ω ↦ rightLimWithin (X · ω) T t) := by
  rcases (𝓝[T ∩ Set.Ioi t] t).eq_or_neBot with hlbot | hlne
  · -- If the right neighbourhood filter is trivial, the right limit is just `X t`.
    have heq : (fun ω ↦ Function.rightLimWithin (X · ω) T t) = X t := by
      ext ω
      exact rightLimWithin_eq_of_eq_bot _ (by rw [Set.inter_comm]; exact hlbot)
    rw [heq]
    exact (hX t).mono (𝓕.le _) le_rfl
  · -- The set where the right limit exists is `𝓕 t`-measurable.
    have hAmeas : MeasurableSet {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)} :=
      ProbabilityTheory.measurableSet_tendsto_nhdsGT' hT hX t
    -- Off that set, the right limit equals `X t`.
    have hoffA ω (hω : ¬ (∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l))) :
        Function.rightLimWithin (X · ω) T t = X t ω := by
      refine rightLimWithin_eq_of_not_tendsto _ ?_
      rw [Set.inter_comm]
      exact hω
    -- A measurable version of the right limit along the countable index `↥S`, `S ⊆ (t, s)`.
    set S : Set ι := (T ∩ Set.Ioi t) with hSdef
    have hScount : S.Countable := hT.mono (Set.inter_subset_left)
    have : Countable ↥S := hScount.to_subtype
    set l₀ : Filter ↥S := Filter.comap ((↑) : ↥S → ι) (𝓝[T ∩ Set.Ioi t] t) with hl₀
    have : l₀.IsCountablyGenerated := by rw [hl₀]; infer_instance
    have hmap : Filter.map ((↑) : ↥S → ι) l₀ = 𝓝[T ∩ Set.Ioi t] t :=
      Filter.map_comap_of_mem (by rw [Subtype.range_coe]; exact self_mem_nhdsWithin)
    have : l₀.NeBot := by
      constructor
      intro h
      rw [h, Filter.map_bot] at hmap
      exact hlne.ne' hmap.symm
    -- The measurable candidate.
    have hf (s' : ↥S) : Measurable (fun ω => X ↑s' ω) :=
      (hX ↑s').mono (𝓕.le _) le_rfl
    have hgmeas : Measurable (fun ω => limUnder l₀ (fun s' : ↥S => X ↑s' ω)) :=
      @_root_.Prove2MeSourceProof.h_cba8008674f3dd8a34a01708 ↥S Ω ℝ mΩ _ _ _ _ _ l₀ _ _ _ hf
    -- On the set where the limit exists, the candidate is the right limit.
    have hgA (ω : Ω) (hω : ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)) :
        limUnder l₀ (fun s' : ↥S ↦ X ↑s' ω) = Function.rightLimWithin (X · ω) T t := by
      rw [Set.inter_comm] at hω
      have htend := tendsto_rightLimWithin_of_tendsto hω
      rw [Set.inter_comm, ← hmap, tendsto_map'_iff] at htend
      exact htend.limUnder_eq
    -- Assemble via `piecewise`.
    classical
    have hpw : (fun ω ↦ Function.rightLimWithin (X · ω) T t)
        = {ω | ∃ l, Tendsto (X · ω) (𝓝[T ∩ Set.Ioi t] t) (𝓝 l)}.piecewise
            (fun ω ↦ limUnder l₀ (fun s' : ↥S => X ↑s' ω)) (X t) := by
      funext ω
      simp only [Set.piecewise]
      split_ifs with hω
      · exact (hgA ω hω).symm
      · exact hoffA ω hω
    rw [hpw]
    refine Measurable.piecewise ?_ hgmeas ?_
    · exact hAmeas
    · exact (hX t).mono (𝓕.le _) le_rfl
/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModif X` with the following properties:
* `rightContModif X` is right-continuous
* `rightContModif X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModif X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModif X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModif X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

/-! ## Càdlàg modification of a quasimartingale

For a real quasimartingale `X` we define a process `cadlagModif X` with the following properties:
* `cadlagModif X` is càdlàg
* for all `t` outside a countable set, `cadlagModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `cadlagModif X` is a modification of `X`.
* if the filtration is right-continuous and complete, then `cadlagModif X` is adapted.

TODO: if `t ↦ μ[X t]` is right-continuous (in particular if `X` is a martingale),
then `cadlagModif X` is a modification of `X` without the assumption that `X`
is right-continuous in probability.

-/

end ProbabilityTheory


