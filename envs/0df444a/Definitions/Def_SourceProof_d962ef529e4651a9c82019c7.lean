-- Prove2me | Definitions.Def_SourceProof_d962ef529e4651a9c82019c7
-- name    : SourceProof_d962ef529e4651a9c82019c7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:46:48.252908+00:00
-- url     : https://prove2.me/theorems/8803cfbf-4c49-55fb-aca5-49e72e0db881
-- title:
--   StochLean source theorem: MeasureTheory.StronglyMeasurable.isStronglyPredictable_indicator_stoppingTime_le

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
import Definitions.Def_SourceProof_7e5e5377677b42d2d6c2ca59

open private measurableSet_predictable_univ_prod_initial from Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing predictable stopped information at its lifetime

A predictable lifetime has a predictable closed-future region. The source
announcing convention only gives almost-sure convergence; initial completeness
repairs the exceptional paths without changing the original lifetime or its
finite-time graph. Right continuity of the filtration and finiteness of the
measure are not needed.

A coefficient measurable strictly before this lifetime can be revealed at and
after it to obtain an actual strongly predictable process. The proof uses the
before-field generators on the closed-future region, and does not regard the
coefficient as initial information. At lifetime zero the coefficient is already
initial information. At infinite lifetime every finite-time value is zero,
regardless of the coefficient there; no value of a process at infinity is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

namespace StronglyMeasurable

theorem _root_.Prove2MeSourceProof.h_d962ef529e4651a9c82019c7
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[hτ.1.measurableSpaceBefore] Z) :
    IsStronglyPredictable F
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  classical
  let U : Set (ℝ≥0 × Ω) := {p | τ p.2 ≤ (p.1 : WithTop ℝ≥0)}
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hU : MeasurableSet U := (_root_.Prove2MeSourceProof.h_7e5e5377677b42d2d6c2ca59 hτ) hc0
  have hg : @Measurable U Ω _ hτ.1.measurableSpaceBefore (fun p ↦ p.val.2) := by
    apply Measurable.of_le_map
    change F 0 ⊔ MeasurableSpace.generateFrom _ ≤ _
    refine sup_le ?_ (MeasurableSpace.generateFrom_le ?_)
    · intro A hA
      change MeasurableSet ((fun p : U ↦ p.val.2) ⁻¹' A)
      simpa only [univ_prod, preimage_preimage, Function.comp_def] using
        measurable_subtype_coe (measurableSet_predictable_univ_prod_initial hA)
    · rintro _ ⟨s, A, hA, rfl⟩
      change MeasurableSet
        ((fun p : U ↦ p.val.2) ⁻¹' (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}))
      have he : (fun p : U ↦ p.val.2) ⁻¹' (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω}) =
          (Subtype.val : U → ℝ≥0 × Ω) ⁻¹'
            (Ioi s ×ˢ (A ∩ {ω | (s : WithTop ℝ≥0) < τ ω})) := by
        ext p
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi]
        exact ⟨fun h ↦ ⟨WithTop.coe_lt_coe.mp (h.2.trans_le p.property), h⟩,
          fun h ↦ h.2⟩
      rw [he]
      exact measurable_subtype_coe
        (measurableSet_predictable_Ioi_prod (hA.inter (hτ.1.measurableSet_gt s)))
  change StronglyMeasurable (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2))
  apply stronglyMeasurable_of_restrict_of_restrict_compl hU
  · have he : U.domRestrict (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2)) =
        (fun p : U ↦ Z p.val.2) := by
      funext p
      exact indicator_of_mem p.property _
    rw [he]
    exact hZ.comp_measurable hg
  · have he : Uᶜ.domRestrict (U.indicator (fun p : ℝ≥0 × Ω ↦ Z p.2)) =
        (fun _ : (Uᶜ : Set (ℝ≥0 × Ω)) ↦ (0 : ℝ)) := by
      funext p
      exact indicator_of_notMem p.property _
    rw [he]
    exact stronglyMeasurable_const
end StronglyMeasurable

end MeasureTheory


