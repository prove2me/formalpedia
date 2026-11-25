-- Prove2me | Definitions.Def_SourceProof_3a166a4b79608884a0fedaba
-- name    : SourceProof_3a166a4b79608884a0fedaba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:46:08.298118+00:00
-- url     : https://prove2.me/theorems/9abb9565-1f76-44ba-9d95-6e51637d7fd5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAccessibleStoppingTime.exists_predictable_compensator_indicator

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_PredictableStepSeries_F000
import Definitions.Def_SourceProof_123d5fff674a590c76d89c3f
import Definitions.Def_SourceProof_14e908939680537161478394
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_5d48851af50d099acaedbd72
import Definitions.Def_SourceProof_640bd85f93662d293ed47469
import Definitions.Def_SourceProof_687ae03ee7e823ef9eb6fe66
import Definitions.Def_SourceProof_7270b3ab7a1632573e0ea3ed
import Definitions.Def_SourceProof_a02883e32df61ba595b3947d
import Definitions.Def_SourceProof_a75e1bf0df069c88b46cb594
import Definitions.Def_SourceProof_b0cc873f1a7c7dfe9b126812
import Definitions.Def_SourceProof_bdb573aab3428152bd91f0a3
import Definitions.Def_SourceProof_f40b7170db65e65ad7d3fbe4
import Definitions.Def_SourceProof_f5388bf1d6c6e2332e143c83
import Mathlib.Probability.Martingale.OptionalSampling

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual compensation of integrable accessible single jumps

The existing accessible-time definition supplies a predictable graph cover.
Its actual disjoint positive refinement decomposes the original coefficient
into stopped-measurable pieces with summable first absolute moments. Each
piece is conditioned before its own predictable lifetime. Their actual step
series constructs the predictable integrable-variation compensator.

The centered series is a genuine UI martingale. Absolute summability and the
common-event graph identity identify it with the original jump minus the
constructed compensator. No infinite-time process value, proposed compensator,
or assumed series convergence enters the source hypotheses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {σ : Ω → WithTop ℝ≥0} {D : Ω → ℝ}

namespace IsAccessibleStoppingTime

theorem _root_.Prove2MeSourceProof.h_3a166a4b79608884a0fedaba
    (hσ : IsAccessibleStoppingTime F σ P) (hF : F.IsUsual P)
    (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hm : StronglyMeasurable[hσ.1.measurableSpace] D) (hi : Integrable D P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 =ᵐ[P] 0 ∧
      HasIntegrableVariation A P ∧
      (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖D ω‖ ∂P ∧
      IsUIMartingale
        ((fun t : ℝ≥0 ↦ {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D) - A) F P := by
  classical
  obtain ⟨Γ, hΓ, hpΓ, _, _, hmC, hiC, hsC, hbC, heC⟩ :=
    (_root_.Prove2MeSourceProof.h_640bd85f93662d293ed47469 hσ) hF hpos hm hi
  let C : ℕ → Ω → ℝ := fun n ↦ {ω | σ ω = Γ n ω ∧ σ ω ≠ ⊤}.indicator D
  let K : ℕ → Ω → ℝ := fun n ↦ P[C n | (hΓ n).1.measurableSpaceBefore]
  have hCK : ∀ n, StronglyMeasurable[(hΓ n).1.measurableSpaceBefore] (K n) :=
    fun _ ↦ stronglyMeasurable_condExp
  have hiK (n : ℕ) : Integrable (K n) P := integrable_condExp
  have hsumC : Summable (fun n ↦ ∫ ω, ‖C n ω‖ ∂P) := by
    simpa only [Real.norm_eq_abs] using hsC.summable
  have hnormK (n : ℕ) : (∫ ω, ‖K n ω‖ ∂P) ≤ ∫ ω, ‖C n ω‖ ∂P :=
    integral_norm_condExp_le (C n)
  have hsumK : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P) :=
    hsumC.of_nonneg_of_le (fun n ↦ integral_nonneg fun ω ↦ norm_nonneg (K n ω)) hnormK
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦
    ∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  have hpA : IsStronglyPredictable F A :=
    _root_.Prove2MeSourceProof.h_b0cc873f1a7c7dfe9b126812 hΓ (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) hCK
  have hvA : ProbabilityTheory.HasIntegrableVariation A P :=
    _root_.Prove2MeSourceProof.h_f5388bf1d6c6e2332e143c83 hF hΓ hCK hiK hsumK
  refine ⟨A, hpA, _root_.Prove2MeSourceProof.h_687ae03ee7e823ef9eb6fe66 Γ hiK hsumK,
    _root_.Prove2MeSourceProof.h_123d5fff674a590c76d89c3f (fun n ↦ Eventually.of_forall (hpΓ n)), hvA, ?_, ?_⟩
  · refine (_root_.Prove2MeSourceProof.h_a75e1bf0df069c88b46cb594
      hF hΓ hCK hiK hsumK).trans ((hsumK.tsum_le_tsum hnormK hsumC).trans ?_)
    simpa only [Real.norm_eq_abs] using hbC
  · have hUI := _root_.Prove2MeSourceProof.h_5d48851af50d099acaedbd72
      (fun n ↦ (hΓ n).1) hmC hiC hsumC
    apply (_root_.Prove2MeSourceProof.h_bdb573aab3428152bd91f0a3 hUI)
      (fun t ↦ ((fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed p2mMethodArg0 hm) hσ.1 t).measurable.sub
        (hpA.stronglyAdapted t).measurable)
    filter_upwards [heC, (_root_.Prove2MeSourceProof.h_14e908939680537161478394 hiC hsumC).1,
      (_root_.Prove2MeSourceProof.h_14e908939680537161478394 hiK hsumK).1] with ω he hC hK t
    have hsCstep : Summable
        (fun n ↦ {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n) ω) :=
      hC.of_norm_bounded (fun _ ↦ norm_indicator_le_norm_self _ _)
    have hsKstep : Summable
        (fun n ↦ {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) :=
      hK.of_norm_bounded (fun _ ↦ norm_indicator_le_norm_self _ _)
    change (∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n - K n) ω) =
      {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D ω - A t ω
    have hsub (n : ℕ) :
        {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n - K n) ω =
          {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n) ω -
            {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω :=
      congrFun (indicator_sub {ω | Γ n ω ≤ (t : WithTop ℝ≥0)} (C n) (K n)) ω
    rw [tsum_congr hsub, hsCstep.tsum_sub hsKstep, ← he t]
end IsAccessibleStoppingTime

end ProbabilityTheory


