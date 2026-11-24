-- Prove2me | Definitions.Def_StochLean_Probability_Process_Filtration_StoppingTimeReindex_F000
-- name    : StochLean_Probability_Process_Filtration_StoppingTimeReindex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:44.256145+00:00
-- url     : https://prove2.me/theorems/c371cf0a-e24d-401d-8609-71a9212f5170
-- title:
--   StochLean: Probability.Process.Filtration.StoppingTimeReindex F000

import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reindexing a filtration by an ordered family of stopping times -/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]

/-- The sampled filtration consists of the canonical stopping-time sigma-algebras.
Its construction does not assume that the stopping times are finite or bounded. -/
def Filtration.stoppingTimeReindex (F : Filtration ℝ≥0 mΩ)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ) :
    Filtration ι mΩ :=
  ⟨fun i ↦ (hτ i).measurableSpace,
    fun _ _ hij ↦ (hτ _).measurableSpace_mono (hτ _) (hmono hij),
    fun i ↦ (hτ i).measurableSpace_le⟩
end MeasureTheory


