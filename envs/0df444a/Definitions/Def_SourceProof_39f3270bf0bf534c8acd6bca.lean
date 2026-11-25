-- Prove2me | Definitions.Def_SourceProof_39f3270bf0bf534c8acd6bca
-- name    : SourceProof_39f3270bf0bf534c8acd6bca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:04.676468+00:00
-- url     : https://prove2.me/theorems/f7cf48b4-c1c6-5c2c-a1d5-ebb42b17b20b
-- title:
--   StochLean source theorem: MeasureTheory.martingale_indicator_stoppingTime_le_of_condExp_before_eq_zero

import Definitions.Def_StochLean_Probability_Process_ClassD_Basic_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_3f8c9bee8c801981db97d019
import Definitions.Def_SourceProof_7270b3ab7a1632573e0ea3ed
import Definitions.Def_SourceProof_7697f46ddf08897a14ff00d9
import Definitions.Def_SourceProof_963ead9a91977c0b480ddda0
import Definitions.Def_SourceProof_dfa9835b65113f9bb1f932de
import Definitions.Def_SourceProof_fc0f2624190866d48e0e4775
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Before-centered integrable single jumps are UI martingales

The coefficient is measurable at the stopping time, not necessarily before it.
If its conditional expectation before that time vanishes, its actual closed
lifetime step is a martingale. Integrable domination of all stopping values
gives Class D and hence uniform integrability.

No predictability of the lifetime is needed for this centered martingale
statement. Predictability is needed separately to identify the removed
before-conditional step as a predictable compensating process. Infinite
lifetimes never activate at finite time; coefficients are not assumed zero
there and no finite evaluation of an infinite stopping time is used.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_39f3270bf0bf534c8acd6bca
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) (hz : P[Z | hτ.measurableSpaceBefore] =ᵐ[P] 0) :
    Martingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P := by
  classical
  let J : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z
  have hD := _root_.Prove2MeSourceProof.h_7697f46ddf08897a14ff00d9 hτ hm hi
  refine ⟨fun t ↦ (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed p2mMethodArg0 hm) hτ t, ?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) ((_root_.Prove2MeSourceProof.h_fc0f2624190866d48e0e4775 hD) t)
    (fun _ _ _ ↦ ((_root_.Prove2MeSourceProof.h_fc0f2624190866d48e0e4775 hD) s).integrableOn) _
    ((fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed p2mMethodArg0 hm) hτ s).aestronglyMeasurable
  intro A hA _
  let B : Set Ω := (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) ∩
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}
  have hBt : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    simpa only [compl_ofPred, not_lt] using ((_root_.Prove2MeSourceProof.h_963ead9a91977c0b480ddda0 hτ) t).compl
  have hB : MeasurableSet[hτ.measurableSpaceBefore] B :=
    ((_root_.Prove2MeSourceProof.h_dfa9835b65113f9bb1f932de hτ) s hA).inter hBt
  have hBambient : MeasurableSet B := (_root_.Prove2MeSourceProof.h_3f8c9bee8c801981db97d019 hτ) _ hB
  have hzero : (∫ ω in B, Z ω ∂P) = 0 := by
    calc
      _ = ∫ ω in B, P[Z | hτ.measurableSpaceBefore] ω ∂P :=
        (setIntegral_condExp (_root_.Prove2MeSourceProof.h_3f8c9bee8c801981db97d019 hτ) hi hB).symm
      _ = ∫ ω in B, (0 : Ω → ℝ) ω ∂P := integral_congr_ae (ae_restrict_of_ae hz)
      _ = 0 := by simp
  have he : A.indicator (J t - J s) = B.indicator Z := by
    funext ω
    simp only [J, B, indicator_apply, Pi.sub_apply, mem_inter_iff, mem_ofPred_eq]
    by_cases hAω : ω ∈ A
    · by_cases hs : τ ω ≤ (s : WithTop ℝ≥0)
      · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
        have hns := not_lt.mpr hs
        simp only [hAω, hs, ht, hns, if_true, if_false, and_false, false_and, sub_self]
      · have hss : (s : WithTop ℝ≥0) < τ ω := lt_of_not_ge hs
        by_cases ht : τ ω ≤ (t : WithTop ℝ≥0) <;>
          simp only [hAω, hs, ht, hss, if_true, if_false, and_self, and_false,
            sub_zero, sub_self]
    · simp only [hAω, false_and, if_false]
  have hd : (∫ ω in A, J t ω ∂P) - (∫ ω in A, J s ω ∂P) = 0 := by
    rw [← integral_sub ((_root_.Prove2MeSourceProof.h_fc0f2624190866d48e0e4775 hD) t).integrableOn ((_root_.Prove2MeSourceProof.h_fc0f2624190866d48e0e4775 hD) s).integrableOn]
    change (∫ ω in A, (J t - J s) ω ∂P) = 0
    rw [← integral_indicator (F.le s _ hA), he, integral_indicator hBambient]
    exact hzero
  exact (sub_eq_zero.mp hd).symm
end MeasureTheory


