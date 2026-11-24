-- Prove2me | Definitions.Def_StochLean_Probability_Process_Filtration_Terminal_F000
-- name    : StochLean_Probability_Process_Filtration_Terminal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:46.4488+00:00
-- url     : https://prove2.me/theorems/4130d568-9e43-49c2-97d4-02accef66eb6
-- title:
--   Terminal extension of a filtration
-- statement:
--   The filtration is extended to an infinite time index using the supremum of the finite-time sigma-algebras.

import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Extending the time index by its terminal sigma-field

The terminal sigma-field is the supremum of the finite-time filtration,
not the ambient measurable space. This agrees with the existing stopping
sigma-field at the constant infinite stopping time.
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def Filtration.withTerminal (F : Filtration ℝ≥0 mΩ) : Filtration (WithTop ℝ≥0) mΩ :=
  ⟨fun t ↦ WithTop.recTopCoe (⨆ s, F s) (fun s ↦ F s) t, by
    intro i j hij
    cases i using WithTop.recTopCoe with
    | top =>
      have hj : j = ⊤ := top_le_iff.mp hij
      subst j
      exact le_rfl
    | coe i =>
      cases j using WithTop.recTopCoe with
      | top => exact le_iSup (fun s ↦ F s) i
      | coe j => exact F.mono (WithTop.coe_le_coe.mp hij), by
    intro t
    cases t using WithTop.recTopCoe with
    | top => exact iSup_le F.le
    | coe t => exact F.le t⟩
end MeasureTheory


