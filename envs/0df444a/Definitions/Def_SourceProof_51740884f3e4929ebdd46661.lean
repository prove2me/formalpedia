-- Prove2me | Definitions.Def_SourceProof_51740884f3e4929ebdd46661
-- name    : SourceProof_51740884f3e4929ebdd46661
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:34.405669+00:00
-- url     : https://prove2.me/theorems/39ff653a-d313-4cef-a122-51eca1796904
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSpaceBefore_le

import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The sigma-field strictly before a stopping time

Protter III.2 defines `F_{T-}` using `F_0` and the events `A ∩ {t < T}`,
where `A ∈ F_t` and `t > 0`. We allow `t = 0` in the sole owner below and
prove that this gives exactly the same sigma-field. This is a subfield of
Mathlib's existing stopped sigma-field, not a replacement for it.

At infinite lifetime this field is `⨆ t, F t`, not necessarily `F_0` or
the ambient sigma-field. No process value at infinity is defined here.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_51740884f3e4929ebdd46661 (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore ≤ hτ.measurableSpace := by
  refine sup_le (hτ.le_measurableSpace_of_const_le fun _ ↦ bot_le)
    (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨t, A, hA, rfl⟩
  refine ⟨le_iSup F t _ (hA.inter (hτ.measurableSet_gt t)), fun u ↦ ?_⟩
  by_cases hut : u ≤ t
  · have he : (A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}) ∩ {ω | τ ω ≤ u} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hω hle
      exact (not_lt_of_ge (hle.trans (WithTop.coe_le_coe.mpr hut))) hω.2
    rw [he]
    exact @MeasurableSet.empty Ω (F u)
  · exact ((F.mono (le_of_not_ge hut) _ hA).inter
      (F.mono (le_of_not_ge hut) _ (hτ.measurableSet_gt t))).inter (hτ u)
end MeasureTheory.IsStoppingTime


