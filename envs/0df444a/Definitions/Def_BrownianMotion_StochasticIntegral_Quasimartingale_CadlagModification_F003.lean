-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F003
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:33:57.339725+00:00
-- url     : https://prove2.me/theorems/0126bf36-834f-461d-a495-cb301612207a
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F002
import Definitions.Def_SourceProof_9a7ee104958c92f51ae1a7a7
import Definitions.Def_SourceProof_ce2182052ee14161adc2c6b8

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

lemma adapted_rightContModif [SecondCountableTopology ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (rightContModif X) := by
  refine fun i ↦ Measurable.ite
    (measurableSet_regularitySetRight hX countable_denseCountable dense_denseCountable i) ?_
    (by fun_prop)
  exact _root_.Prove2MeSourceProof.h_9a7ee104958c92f51ae1a7a7 countable_denseCountable hX.stronglyAdapted.adapted i
lemma stronglyAdapted_rightContModif [SecondCountableTopology ι] [𝓕.IsRightContinuous]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (rightContModif X) :=
  (adapted_rightContModif hX).stronglyAdapted
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

/-- The càdlàg modification of a real quasimartingale along a countable dense set `T`. -/
noncomputable
def cadlagModif [SecondCountableTopology ι] (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  open Classical in
  if ∀ t, ω ∈ regularitySetRight (denseCountable ι) X t then rightContModif X t ω else 0
omit [DenselyOrdered ι] in
lemma cadlagModif_ae_eq_rightContModif [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    ∀ᵐ ω ∂μ, ∀ t, cadlagModif X t ω = rightContModif X t ω := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    dense_denseCountable.exists_gt] with ω hω
  simp [cadlagModif, if_pos hω]
omit [DenselyOrdered ι] in
lemma measurable_cadlagModif [SecondCountableTopology ι]
    (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (cadlagModif X t) := by
  refine Measurable.ite ?_ (measurable_rightContModif hX t) (by fun_prop)
  have : {a | ∀ (t : ι), a ∈ regularitySetRight (denseCountable ι) X t}
      = ⋂ t ∈ denseCountable ι, regularitySetRight (denseCountable ι) X t := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h t _ ↦ h t, fun h t ↦ ?_⟩
    obtain ⟨t', ht'T, htt'⟩ := dense_denseCountable.exists_gt t
    specialize h t' ht'T
    exact regularitySetRight_anti htt'.le h
  rw [this]
  exact MeasurableSet.biInter countable_denseCountable
    fun t _ ↦ measurableSet_regularitySetRight' hX countable_denseCountable t
omit [OrderBot ι] in
lemma continuousWithinAt_cadlagModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ContinuousWithinAt (cadlagModif X · ω) (Set.Ioi x) x := by
  unfold cadlagModif
  split_ifs with hω
  · exact continuousWithinAt_rightContModif x ω
  · fun_prop
omit [OrderBot ι] in
lemma exists_tendsto_nhdsLT_cadlagModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ∃ l, Tendsto (cadlagModif X · ω) (𝓝[<] x) (𝓝 l) := by
  unfold cadlagModif
  split_ifs with hω
  · exact ⟨Function.leftLimWithin (X · ω) (denseCountable ι) x,
      tendsto_rightContModif_leftLimWithin (hω x)⟩
  · exact ⟨0, tendsto_const_nhds⟩
omit [OrderBot ι] in
lemma isCadlag_cadlagModif [SecondCountableTopology ι] (ω : Ω) :
    IsCadlag (cadlagModif X · ω) := by
  constructor
  · exact fun x ↦ continuousWithinAt_cadlagModif x ω
  · exact fun x ↦ exists_tendsto_nhdsLT_cadlagModif x ω
omit [DenselyOrdered ι] in
lemma cadlagModif_ae_eq_of_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (denseCountable ι) t) =ᵐ[μ] X t) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    dense_denseCountable.exists_gt, ht] with ω hω hωR
  simpa only [cadlagModif, if_pos hω, rightContModif, if_pos (hω t)]
/-- The set of points where the cadlag modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_cadlagModif_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ cadlagModif X t =ᵐ[μ] X t}.Countable := by
  refine (_root_.Prove2MeSourceProof.h_168e7570e1f716d3568af3a2 hX countable_denseCountable dense_denseCountable).mono
    fun t ht ↦ ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  refine fun h_contra ↦ ht ?_
  filter_upwards [cadlagModif_ae_eq_rightContModif hX,
    rightContModif_ae_eq_of_rightLimWithin_ae_eq hX h_contra] with ω hω hωc
  grind
lemma cadlagModif_ae_eq_of_tendstoInMeasure [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    cadlagModif X t =ᵐ[μ] X t := by
  filter_upwards [cadlagModif_ae_eq_rightContModif hX,
    _root_.Prove2MeSourceProof.h_ce2182052ee14161adc2c6b8 hX t hXRC] with ω hω hωc
  grind
lemma adapted_cadlagModif [SecondCountableTopology ι] [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    Adapted 𝓕 (cadlagModif X) := by
  refine fun i ↦ Measurable.ite ?_ (adapted_rightContModif hX i)
    (by fun_prop)
  rw [← MeasurableSet.compl_iff]
  refine Filtration.IsComplete.measurableSet_of_null ?_ i (μ := μ)
  have h := ae_mem_regularitySetRight hX countable_denseCountable dense_denseCountable.exists_gt
  rwa [ae_iff] at h
lemma stronglyAdapted_cadlagModif [SecondCountableTopology ι] [𝓕.IsRightContinuous] [𝓕.IsComplete μ]
    [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 (cadlagModif X) :=
  (adapted_cadlagModif hX).stronglyAdapted
end ProbabilityTheory


