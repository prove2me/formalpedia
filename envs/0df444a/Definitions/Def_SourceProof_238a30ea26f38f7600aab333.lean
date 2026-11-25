-- Prove2me | Definitions.Def_SourceProof_238a30ea26f38f7600aab333
-- name    : SourceProof_238a30ea26f38f7600aab333
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:30:50.173923+00:00
-- url     : https://prove2.me/theorems/f1d1271f-8c3c-5cbe-ba6c-095471e721d0
-- title:
--   StochLean source theorem: MeasureTheory.Filtration.predictable_le_optional

import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Definitions.Def_SourceProof_a668d32c17f2633459e41237

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The optional sigma-field and the source inclusion chain

Protter III.1 defines the optional sigma-field using adapted cadlag real
processes. Everywhere path regularity is used in its generators. For merely
almost-sure cadlag paths the bridge constructs an indistinguishable optional
version; it does not assert optionality of arbitrary exceptional trajectories.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Filtration

end Filtration

namespace Filtration


theorem _root_.Prove2MeSourceProof.h_238a30ea26f38f7600aab333 (F : Filtration ℝ≥0 mΩ) : F.predictable ≤ F.optional := by
  classical
  have hclock : Measurable[F.optional] (fun p : ℝ≥0 × Ω ↦ (p.1 : ℝ)) := by
    apply _root_.Prove2MeSourceProof.h_a668d32c17f2633459e41237 (X := fun t _ ↦ (t : ℝ))
    · exact fun _ ↦ measurable_const
    · exact fun _ ↦ _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 NNReal.continuous_coe
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    let V : Ω → ℝ := A.indicator (fun _ ↦ 1)
    have ha : Adapted F (fun (_ : ℝ≥0) ↦ V) :=
      fun t ↦ measurable_const.indicator (F.mono bot_le _ hA)
    have hm := (_root_.Prove2MeSourceProof.h_a668d32c17f2633459e41237 ha)
      (fun _ ↦ _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const)
    have hs := (hclock (measurableSet_singleton 0)).inter (hm (measurableSet_singleton 1))
    convert hs using 1
    ext ⟨t, ω⟩
    simp [V]
  · intro a A hA
    let V : Ω → ℝ := A.indicator (fun _ ↦ 1)
    let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ ((t - a : ℝ≥0) : ℝ) * V ω
    have ha : Adapted F X := by
      intro t
      by_cases ht : a ≤ t
      · exact measurable_const.mul (measurable_const.indicator (F.mono ht _ hA))
      · have he : X t = 0 := by
          funext ω
          simp only [X, tsub_eq_zero_of_le (le_of_not_ge ht), NNReal.coe_zero, zero_mul,
            Pi.zero_apply]
        rw [he]
        exact measurable_const
    have hc : ∀ ω, ProbabilityTheory.IsCadlagPath (fun t ↦ X t ω) := by
      intro ω
      apply _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121
      change Continuous (fun t : ℝ≥0 ↦ ((t - a : ℝ≥0) : ℝ) * V ω)
      fun_prop
    have hm := (_root_.Prove2MeSourceProof.h_a668d32c17f2633459e41237 ha) hc
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))
    convert hm using 1
    ext ⟨t, ω⟩
    change (a < t ∧ ω ∈ A) ↔ 0 < X t ω
    by_cases hω : ω ∈ A
    · simp [X, V, hω, NNReal.coe_pos, tsub_pos_iff_lt]
    · simp [X, V, hω]
end Filtration

variable {E : Type*} [TopologicalSpace E] {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


