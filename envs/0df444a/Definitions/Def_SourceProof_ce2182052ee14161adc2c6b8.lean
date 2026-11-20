-- Prove2me | Definitions.Def_SourceProof_ce2182052ee14161adc2c6b8
-- name    : SourceProof_ce2182052ee14161adc2c6b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:32:54.019636+00:00
-- url     : https://prove2.me/theorems/4d0976fd-92e1-4c04-a8e6-fbb3b50ea2c1
-- title:
--   LevyStochCalc source module: SourceProof_ce2182052ee14161adc2c6b8
-- statement:
--   The original source theorem `ProbabilityTheory.rightContModif_ae_eq_of_tendstoInMeasure` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F002
import Definitions.Def_SourceProof_ff2308ed19a09ceb00275866

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

theorem _root_.Prove2MeSourceProof.h_ce2182052ee14161adc2c6b8 [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModif X t =ᵐ[μ] X t := by
  classical
  let Y := ProbabilityTheory.rightContModif X
  have hY_meas t : Measurable (Y t) := ProbabilityTheory.measurable_rightContModif hX t
  have hYCont x ω: ContinuousWithinAt (Y · ω) (Set.Ioi x) x :=
    ProbabilityTheory.continuousWithinAt_rightContModif x ω
  let T := denseCountable ι
  have hTc : T.Countable := countable_denseCountable
  have hTd : Dense T := dense_denseCountable
  have hX_cont x : ∀ᵐ ω ∂μ, Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (Y x ω)) := by
    have hX_cont' x ω (hω : ω ∈ ProbabilityTheory.regularitySetRight T X x) :
        Tendsto (X · ω) (𝓝[>] x ⊓ 𝓟 T) (𝓝 (Function.rightLimWithin (X · ω) T x)) := by
      rw [nhdsWithin_inf_principal, Set.inter_comm]
      exact ProbabilityTheory.tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
    have h1 := ProbabilityTheory.ae_mem_regularitySetRight hX hTc hTd.exists_gt
    filter_upwards [h1] with ω hω using by grind [ProbabilityTheory.rightContModif]
  have : (𝓝[Set.Ioi t ∩ T] t).NeBot := nhdsWithin_Ioi_inter_neBot hTd t
  obtain ⟨w, hseq'⟩ := exists_seq_tendsto (𝓝[Set.Ioi t ∩ T] t)
  obtain hseq : Tendsto w atTop (𝓝[>] t) := by
    rw [tendsto_nhdsWithin_iff] at hseq' ⊢
    refine ⟨hseq'.1, ?_⟩
    filter_upwards [hseq'.2] with n hn using by grind
  refine tendstoInMeasure_ae_unique ?_ ?_ (f := Y ∘ w) (u := atTop)
  · refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
    · exact (hY_meas (w n)).aestronglyMeasurable
    · exact ae_of_all _ fun ω ↦ (hYCont t ω).tendsto.comp hseq
  suffices TendstoInMeasure μ (fun k ω ↦ Y (w k) ω - X (w k) ω) atTop 0 by
    have hX_tendsto := hXRC.comp hseq
    have h_eq : Y ∘ w = (fun k ω ↦ Y (w k) ω - X (w k) ω) + (X ∘ w) := by ext; simp
    rw [h_eq, ← zero_add (X t)]
    exact _root_.Prove2MeSourceProof.h_ff2308ed19a09ceb00275866 this hX_tendsto
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (hY_meas (w n)).stronglyMeasurable.sub ((hX.stronglyAdapted (w n)).mono (𝓕.le _))
  filter_upwards [hX_cont t] with ω hX_cont
  simp only [Pi.zero_apply]
  have : 0 = Y t ω - Y t ω := by simp
  rw [this]
  refine Tendsto.sub ?_ ?_
  · exact (hYCont t ω).tendsto.comp hseq
  · refine hX_cont.comp ?_
    rwa [nhdsWithin_inf_principal]
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


