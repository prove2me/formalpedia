-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F002
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:46:07.016823+00:00
-- url     : https://prove2.me/theorems/1aa60303-b2e4-4cd4-9fe3-a3983b9fee86
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000
import Definitions.Def_SourceProof_0ddf817e0e6cccdfb7b551a7
import Definitions.Def_SourceProof_168e7570e1f716d3568af3a2

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

/-- The right-continuous modification of a real quasimartingale along a countable dense set `T`. -/
noncomputable
def rightContModif [SecondCountableTopology ι] (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  open Classical in
  if ω ∈ regularitySetRight (denseCountable ι) X t
    then rightLimWithin (X · ω) (denseCountable ι) t else 0
omit [DenselyOrdered ι] [NoMaxOrder ι] in
lemma measurable_rightContModif [SecondCountableTopology ι]
    (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (rightContModif X t) := by
  refine Measurable.ite (measurableSet_regularitySetRight' hX countable_denseCountable t) ?_
    (by fun_prop)
  exact _root_.Prove2MeSourceProof.h_0ddf817e0e6cccdfb7b551a7 countable_denseCountable hX.stronglyAdapted.adapted t
omit [OrderBot ι] in
lemma tendsto_rightContModif_rightLimWithin [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
    Tendsto (rightContModif X · ω) (𝓝[>] x) (𝓝 (rightLimWithin (X · ω) (denseCountable ι) x)) := by
  have h_mem : ∀ᶠ y in 𝓝[>] x, ω ∈ regularitySetRight (denseCountable ι) X y :=
    eventually_mem_regularitySetRight_of_mem hω
  classical
  rw [tendsto_congr' (f₂ := rightLimWithin (X · ω) (denseCountable ι))]
  swap; · filter_upwards [h_mem] with s' hs using by grind [rightContModif]
  suffices ContinuousWithinAt (rightLimWithin (X · ω) (denseCountable ι)) (Set.Ici x) x by
    rwa [← continuousWithinAt_Ioi_iff_Ici] at this
  exact rightContinuous_rightLimWithin_of_mem_regularitySetRight dense_denseCountable hω
omit [OrderBot ι] in
lemma tendsto_rightContModif_leftLimWithin [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
    Tendsto (rightContModif X · ω) (𝓝[<] x) (𝓝 (leftLimWithin (X · ω) (denseCountable ι) x)) := by
  let R := fun t ω ↦ rightLimWithin (X · ω) (denseCountable ι) t
  have hRspec x ω (hω : ω ∈ regularitySetRight (denseCountable ι) X x) :
      Tendsto (X · ω) (𝓝[(denseCountable ι) ∩ Set.Ioi x] x) (𝓝 (R x ω)) :=
    tendsto_nhdsGT_rightLimWithin_of_mem_regularitySetRight hω
  let Lc x ω := leftLimWithin (X · ω) (denseCountable ι) x
  have hLspec x ω (h : ∃ l, Tendsto (fun s' ↦ X s' ω) (𝓝[(denseCountable ι) ∩ Set.Iio x] x) (𝓝 l)) :
      Tendsto (fun s' ↦ X s' ω) (𝓝[(denseCountable ι) ∩ Set.Iio x] x) (𝓝 (Lc x ω)) := by
    unfold Lc
    simp_rw [Set.inter_comm (denseCountable ι)] at h ⊢
    exact tendsto_leftLimWithin_of_tendsto h
  have h_mem y (hyx : y ≤ x) : ω ∈ regularitySetRight (denseCountable ι) X y :=
    regularitySetRight_anti hyx hω
  classical
  rw [tendsto_congr' (f₂ := (R · ω))]
  swap; · exact eventually_nhdsWithin_of_forall fun y hy ↦ by grind [rightContModif]
  unfold R
  refine tendsto_rightLim_nhdsLT dense_denseCountable ?_ (hLspec x ω ?_)
  · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    exact hRspec y ω (h_mem y (by grind))
  · exact left_limit_of_mem_regularitySetRight (h_mem x le_rfl) le_rfl
omit [OrderBot ι] [OrderTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] in
lemma rightContModif_eq_zero [SecondCountableTopology ι] {x : ι} {ω : Ω}
    (hω : ω ∉ regularitySetRight (denseCountable ι) X x) :
    (rightContModif  X · ω) =ᶠ[𝓝[>] x] 0 := by
  have h_all y (hy : x ≤ y) : ω ∉ regularitySetRight (denseCountable ι) X y :=
    fun hω' ↦ hω (regularitySetRight_anti hy hω')
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  simp at hy ⊢
  grind [rightContModif]
omit [OrderBot ι] in
lemma continuousWithinAt_rightContModif [SecondCountableTopology ι] (x : ι) (ω : Ω) :
    ContinuousWithinAt (rightContModif X · ω) (Set.Ioi x) x := by
  by_cases hω : ω ∈ regularitySetRight (denseCountable ι) X x
  · have hYx : rightContModif X x ω = rightLimWithin (X · ω) (denseCountable ι) x := by
      simp only [rightContModif, if_pos hω]
    rw [ContinuousWithinAt, hYx]
    exact tendsto_rightContModif_rightLimWithin hω
  · refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (rightContModif_eq_zero hω) ?_
    · fun_prop
    · simp [rightContModif, hω]
omit [DenselyOrdered ι] in
lemma rightContModif_ae_eq_of_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) {t : ι}
    (ht : (fun ω ↦ rightLimWithin (X · ω) (denseCountable ι) t) =ᵐ[μ] X t) :
    rightContModif X t =ᵐ[μ] X t := by
  filter_upwards [ae_mem_regularitySetRight hX countable_denseCountable
    dense_denseCountable.exists_gt, ht] with ω hω hωR
  simpa only [rightContModif, if_pos (hω _)]
/-- The set of points where the right modification of a real quasimartingale along
a countable dense set `T` disagrees with `X` is countable. -/
lemma countable_not_rightContModif_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ) :
    {t | ¬ rightContModif X t =ᵐ[μ] X t}.Countable := by
  refine (_root_.Prove2MeSourceProof.h_168e7570e1f716d3568af3a2 hX countable_denseCountable dense_denseCountable).mono
    fun t ht ↦ ?_
  exact fun hcon ↦ ht (rightContModif_ae_eq_of_rightLimWithin_ae_eq hX hcon)
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


