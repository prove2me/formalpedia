-- Prove2me | Definitions.Def_SourceProof_7e5e5377677b42d2d6c2ca59
-- name    : SourceProof_7e5e5377677b42d2d6c2ca59
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:24.664141+00:00
-- url     : https://prove2.me/theorems/5feb43ee-871f-4a60-b0cb-03b19938011d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.measurableSet_predictable_le

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
import Definitions.Def_SourceProof_35649b1a80f47b6121901d45
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_b631e7db21b69a2eea178eb7

open private measurableSet_predictable_univ_prod_initial measurable_predictable_fst measurable_predictable_snd_initial from Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
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

namespace IsPredictableStoppingTime

theorem _root_.Prove2MeSourceProof.h_7e5e5377677b42d2d6c2ca59
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[F.predictable]
      {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} := by
  classical
  obtain ⟨σ, hσ, _⟩ := (_root_.Prove2MeSourceProof.h_b631e7db21b69a2eea178eb7 hτ)
  let bad : Set Ω := {ω | ¬ Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))}
  have hbad : MeasurableSet[F 0] bad := hc0 bad (ae_iff.mp hσ.tendsto)
  let τbad : Ω → WithTop ℝ≥0 := fun ω ↦ if ω ∈ bad then τ ω else ⊤
  have heBad : (fun _ : Ω ↦ (⊤ : WithTop ℝ≥0)) =ᵐ[P] τbad := by
    filter_upwards [hσ.tendsto] with ω hω
    simp [τbad, bad, hω]
  have hmBad : Measurable[F 0] τbad := (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc0) measurable_const heBad
  have hmBadFuture : MeasurableSet[F.predictable]
      {p : ℝ≥0 × Ω | τbad p.2 ≤ (p.1 : WithTop ℝ≥0)} :=
    measurableSet_le (hmBad.comp measurable_predictable_snd_initial)
      (WithTop.continuous_coe.measurable.comp measurable_predictable_fst)
  have hzero : MeasurableSet[F 0] {ω | τ ω = 0} := by
    have he : {ω | τ ω = 0} = {ω | τ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
    rw [he]
    exact hτ.1 0
  have he : {p : ℝ≥0 × Ω | τ p.2 ≤ (p.1 : WithTop ℝ≥0)} =
      {p : ℝ≥0 × Ω | τbad p.2 ≤ (p.1 : WithTop ℝ≥0)} ∪
      (((univ : Set ℝ≥0) ×ˢ badᶜ) ∩
        (((univ : Set ℝ≥0) ×ˢ {ω | τ ω = 0}) ∪
          ⋂ n : ℕ, {p : ℝ≥0 × Ω | σ n p.2 < (p.1 : WithTop ℝ≥0)})) := by
    ext ⟨t, ω⟩
    by_cases hω : ω ∈ bad
    · simp [τbad, hω]
    · have hlim : Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) := by
        simpa only [bad, mem_ofPred_eq, not_not] using hω
      have hgood : τ ω ≤ (t : WithTop ℝ≥0) ↔
          τ ω = 0 ∨ ∀ n, σ n ω < (t : WithTop ℝ≥0) := by
        constructor
        · intro hle
          by_cases hz : τ ω = 0
          · exact Or.inl hz
          · exact Or.inr fun n ↦
              (hσ.strict n ω (lt_of_le_of_ne bot_le (Ne.symm hz))).trans_le hle
        · rintro (hz | hlt)
          · rw [hz]
            exact bot_le
          · exact le_of_tendsto hlim (Eventually.of_forall fun n ↦ (hlt n).le)
      simpa only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod, mem_univ,
        mem_compl_iff, hω, not_false_eq_true, true_and, mem_iInter, τbad, if_false,
        top_le_iff, WithTop.coe_ne_top, false_or] using hgood
  rw [he]
  exact hmBadFuture.union
    ((measurableSet_predictable_univ_prod_initial hbad.compl).inter
      ((measurableSet_predictable_univ_prod_initial hzero).union
        (MeasurableSet.iInter fun n ↦ (_root_.Prove2MeSourceProof.h_35649b1a80f47b6121901d45 (hσ.isStoppingTime n)))))
end IsPredictableStoppingTime

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

end MeasureTheory


